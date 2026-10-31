/* -*- Source -*-
 * HirToParser: feature-free HIR onto the existing Parser builders.
 *
 * Do not include <cassert> in this file. Parser::assert is a member function
 * and parser.h undefines the macro on purpose; reintroducing it breaks every
 * parser_->assert(node) call below.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/soft_objectives.h"
#include "somtparser/core/asserting.h"
#include "somtparser/core/root_expression_cache.h"
#include "somtparser/hir/packed_linear_io.h"

#include <algorithm>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace SOMTParser::Lower {

using Uir::ErrorCode;
namespace H = Uir::Hir;

namespace {

// Retaining a finite read-only array helper as define-fun-rec hides its cells
// behind whole-array function arguments in downstream projection. A leaf
// macro exposes those cells without recursively expanding other definitions.
// This is an encoding choice only: exceeding the bound keeps the definition
// shared, and never rejects the source function.
bool finiteArrayReadLeaf(const H::FunDecl& function, std::size_t operation_limit) {
    if (!function.recursive_group.empty() || !function.body) { return false; }
    std::unordered_set<std::string> array_parameters;
    for (const H::Binder& binder : function.binders) {
        if (binder.sort.kind == H::SortKind::ARRAY) {
            array_parameters.insert(binder.name);
        }
    }
    if (array_parameters.empty()) { return false; }
    std::unordered_set<const H::Expr*> seen;
    std::vector<const H::Expr*> pending{function.body.get()};
    std::size_t operations = 0;
    bool has_read = false;
    while (!pending.empty()) {
        const H::Expr* expression = pending.back(); pending.pop_back();
        if (!seen.insert(expression).second) { continue; }
        // Array nodes are visited only for an escape (return, equality,
        // store, etc.). The one permitted use is checked at SELECT below.
        if (expression->sort.kind == H::SortKind::ARRAY) { return false; }
        switch (expression->kind) {
        case H::ExprKind::LIT_BOOL:
        case H::ExprKind::LIT_INT:
        case H::ExprKind::LIT_REAL:
        case H::ExprKind::IDENT:
        case H::ExprKind::BOUND_VAR:
            break;
        case H::ExprKind::OP:
            if (++operations >= operation_limit) { return false; }
            if (expression->op == H::Op::SELECT) {
                if (expression->args.size() != 2) { return false; }
                const auto& array = expression->args[0];
                const auto& index = expression->args[1];
                if (array->kind != H::ExprKind::BOUND_VAR
                    || array_parameters.count(array->name) == 0
                    || index->kind != H::ExprKind::LIT_INT) {
                    return false;
                }
                has_read = true;
                // Do not enqueue the permitted array occurrence. The same
                // node used anywhere else must still fail the escape check.
                continue;
            }
            break;
        default:
            // In particular, no APPLY (defined or uninterpreted), quantifier,
            // or other binder can enter the more permissive leaf budget.
            return false;
        }
        for (const auto& child : expression->args) { pending.push_back(child.get()); }
    }
    return has_read;
}

const char* opName(H::Op op) {
    switch (op) {
    // The names a diagnostic uses. div_trunc and div_floor are deliberately
    // NOT spelled "div": what they emit is a correction term around SMT-LIB's
    // div, so a message naming them "div" would send a reader looking for an
    // operator the script does not contain.
    case H::Op::DIV_EUCLID: return "div";
    case H::Op::MOD_EUCLID: return "mod";
    case H::Op::DIV_TRUNC:  return "div_trunc";
    case H::Op::MOD_TRUNC:  return "mod_trunc";
    case H::Op::DIV_FLOOR:  return "div_floor";
    case H::Op::MOD_FLOOR:  return "mod_floor";
    case H::Op::DIV_REAL:   return "/";
    case H::Op::IMPLIES:  return "=>";
    case H::Op::DISTINCT: return "distinct";
    case H::Op::NEG:      return "-";
    case H::Op::ABS:      return "abs";
    case H::Op::AND: return "and";
    case H::Op::OR:  return "or";
    case H::Op::NOT: return "not";
    case H::Op::XOR: return "xor";
    case H::Op::ITE: return "ite";
    case H::Op::EQ:  return "=";
    case H::Op::LE:  return "<=";
    case H::Op::LT:  return "<";
    case H::Op::GE:  return ">=";
    case H::Op::GT:  return ">";
    case H::Op::ADD: return "+";
    case H::Op::SUB: return "-";
    case H::Op::MUL: return "*";
    case H::Op::SELECT: return "select";
    case H::Op::ARRAY_MAP_AND: return "array.map.and";
    case H::Op::ARRAY_MAP_OR: return "array.map.or";
    case H::Op::ARRAY_MAP_NOT: return "array.map.not";
    case H::Op::STORE:  return "store";
    case H::Op::BV_NOT:  return "bvnot";
    case H::Op::BV_NEG:  return "bvneg";
    case H::Op::BV_AND:  return "bvand";
    case H::Op::BV_OR:   return "bvor";
    case H::Op::BV_XOR:  return "bvxor";
    case H::Op::BV_NAND: return "bvnand";
    case H::Op::BV_NOR:  return "bvnor";
    case H::Op::BV_XNOR: return "bvxnor";
    case H::Op::BV_ADD:  return "bvadd";
    case H::Op::BV_SUB:  return "bvsub";
    case H::Op::BV_MUL:  return "bvmul";
    case H::Op::BV_UDIV: return "bvudiv";
    case H::Op::BV_UREM: return "bvurem";
    case H::Op::BV_SDIV: return "bvsdiv";
    case H::Op::BV_SREM: return "bvsrem";
    case H::Op::BV_SMOD: return "bvsmod";
    case H::Op::BV_SHL:  return "bvshl";
    case H::Op::BV_LSHR: return "bvlshr";
    case H::Op::BV_ASHR: return "bvashr";
    case H::Op::BV_ULT:  return "bvult";
    case H::Op::BV_ULE:  return "bvule";
    case H::Op::BV_UGT:  return "bvugt";
    case H::Op::BV_UGE:  return "bvuge";
    case H::Op::BV_SLT:  return "bvslt";
    case H::Op::BV_SLE:  return "bvsle";
    case H::Op::BV_SGT:  return "bvsgt";
    case H::Op::BV_SGE:  return "bvsge";
    case H::Op::BV_CONCAT:      return "concat";
    case H::Op::BV_EXTRACT:     return "extract";
    case H::Op::BV_ROTATE_LEFT: return "rotate_left";
    case H::Op::BV_ROTATE_RIGHT: return "rotate_right";
    case H::Op::BV_REPEAT: return "repeat";
    case H::Op::BV_COMP: return "bvcomp";
    case H::Op::IS_INT: return "is_int";
    case H::Op::IS_DIVISIBLE: return "divisible";
    case H::Op::STR_IS_DIGIT: return "str.is_digit";
    case H::Op::STR_INDEXOF_RE: return "str.indexof_re";
    case H::Op::STR_REPLACE_RE: return "str.replace_re";
    case H::Op::STR_REPLACE_RE_ALL: return "str.replace_re_all";
    case H::Op::CONST_ARRAY: return "const array";
    case H::Op::BV_ZERO_EXTEND: return "zero_extend";
    case H::Op::BV_SIGN_EXTEND: return "sign_extend";
    case H::Op::FP_ADD: return "fp.add";
    case H::Op::FP_SUB: return "fp.sub";
    case H::Op::FP_MUL: return "fp.mul";
    case H::Op::FP_DIV: return "fp.div";
    case H::Op::FP_FMA: return "fp.fma";
    case H::Op::FP_SQRT: return "fp.sqrt";
    case H::Op::FP_ROUND_TO_INTEGRAL: return "fp.roundToIntegral";
    case H::Op::FP_ABS: return "fp.abs";
    case H::Op::FP_NEG: return "fp.neg";
    case H::Op::FP_REM: return "fp.rem";
    case H::Op::FP_MIN: return "fp.min";
    case H::Op::FP_MAX: return "fp.max";
    case H::Op::FP_LEQ: return "fp.leq";
    case H::Op::FP_LT: return "fp.lt";
    case H::Op::FP_GEQ: return "fp.geq";
    case H::Op::FP_GT: return "fp.gt";
    case H::Op::FP_EQ: return "fp.eq";
    case H::Op::FP_IS_NORMAL: return "fp.isNormal";
    case H::Op::FP_IS_SUBNORMAL: return "fp.isSubnormal";
    case H::Op::FP_IS_ZERO: return "fp.isZero";
    case H::Op::FP_IS_INFINITE: return "fp.isInfinite";
    case H::Op::FP_IS_NAN: return "fp.isNaN";
    case H::Op::FP_IS_NEGATIVE: return "fp.isNegative";
    case H::Op::FP_IS_POSITIVE: return "fp.isPositive";
    case H::Op::STR_CONCAT: return "str.++";
    case H::Op::STR_LEN: return "str.len";
    case H::Op::STR_AT: return "str.at";
    case H::Op::STR_SUBSTR: return "str.substr";
    case H::Op::STR_INDEXOF: return "str.indexof";
    case H::Op::STR_REPLACE: return "str.replace";
    case H::Op::STR_REPLACE_ALL: return "str.replace_all";
    case H::Op::STR_CONTAINS: return "str.contains";
    case H::Op::STR_PREFIXOF: return "str.prefixof";
    case H::Op::STR_SUFFIXOF: return "str.suffixof";
    case H::Op::STR_LT: return "str.<";
    case H::Op::STR_LE: return "str.<=";
    case H::Op::STR_TO_INT: return "str.to_int";
    case H::Op::STR_FROM_INT: return "str.from_int";
    case H::Op::STR_TO_CODE: return "str.to_code";
    case H::Op::STR_FROM_CODE: return "str.from_code";
    case H::Op::STR_TO_RE: return "str.to_re";
    case H::Op::STR_IN_RE: return "str.in_re";
    case H::Op::RE_CONCAT: return "re.++";
    case H::Op::RE_UNION: return "re.union";
    case H::Op::RE_INTER: return "re.inter";
    case H::Op::RE_DIFF: return "re.diff";
    case H::Op::RE_STAR: return "re.*";
    case H::Op::RE_PLUS: return "re.+";
    case H::Op::RE_OPT: return "re.opt";
    case H::Op::RE_COMPLEMENT: return "re.comp";
    case H::Op::RE_RANGE: return "re.range";
    case H::Op::RE_LOOP: return "re.loop";
    case H::Op::TO_INT: return "to_int";
    case H::Op::TO_REAL: return "to_real";
    case H::Op::BV_TO_NAT: return "bv2nat";
    case H::Op::BV_TO_INT: return "bv2int";
    case H::Op::INT_TO_BV: return "int2bv";
    case H::Op::FP_TO_REAL: return "fp.to_real";
    case H::Op::FP_TO_IEEE_BV: return "fp.to_ieee_bv";
    case H::Op::FP_TO_SBV: return "fp.to_sbv";
    case H::Op::FP_TO_UBV: return "fp.to_ubv";
    case H::Op::TO_FP: return "to_fp";
    case H::Op::TO_FP_UNSIGNED: return "to_fp_unsigned";
    case H::Op::IEEE_BV_TO_FP: return "to_fp (bit-pattern)";
    case H::Op::SET_SINGLETON: return "set.singleton";
    case H::Op::SET_UNION: return "set.union";
    case H::Op::SET_INTER: return "set.inter";
    case H::Op::SET_MINUS: return "set.minus";
    case H::Op::SET_MEMBER: return "set.member";
    case H::Op::SET_SUBSET: return "set.subset";
    case H::Op::SET_CARD: return "set.card";
    case H::Op::SET_INSERT: return "set.insert";
    case H::Op::SET_COMPLEMENT: return "set.complement";
    case H::Op::TUPLE: return "tuple";
    case H::Op::TUPLE_SELECT: return "tuple.select";
    case H::Op::TUPLE_UPDATE: return "tuple.update";
    case H::Op::TUPLE_PROJECT: return "tuple.project";
    }
    // A new Op must fail here rather than surface as "?" inside a diagnostic
    // message, which would make the error report itself unreadable.
    condAssert(false, "opName: unhandled Hir::Op");
    return "";   // unreachable; condAssert always throws
}

/** Generated names here are SMT simple symbols. Check both their bare and
 * quoted source spelling because `|name|` and `name` have identical identity. */
bool containsSmtSymbol(const std::unordered_set<std::string>& names,
                       const std::string& candidate) {
    return names.count(candidate) != 0
           || names.count('|' + candidate + '|') != 0;
}

} // namespace

/** An HIR sort as one the Parser understands. */
/** Truncating and flooring division built out of SMT-LIB's Euclidean pair.
 *
 * SMT-LIB has exactly one integer division and it is Euclidean: `(div a b)` is
 * the q with `a = b*q + r` and `0 <= r < |b|`, so `(mod a b)` is never
 * negative. The other two conventions are therefore emitted, not mapped.
 *
 * The derivation, written out because a reader has no other way to check it:
 *
 *   Let qe = (div a b) and re = (mod a b), so re is in [0, |b|).
 *
 *   TRUNCATING (C, Java, Go, MiniZinc `div`) rounds toward zero. It agrees with
 *   Euclidean whenever re = 0, and whenever a >= 0 -- for a >= 0 the Euclidean
 *   remainder is already the one truncation produces, whatever the sign of b.
 *   It differs exactly when a < 0 and re != 0, and there q is one step further
 *   toward zero: qt = qe + sign(b), rt = re - |b|.
 *
 *     a=-7 b= 2:  qe=-4 re=1  ->  qt=-3 rt=-1     (-7/2 truncates to -3)
 *     a=-7 b=-2:  qe= 4 re=1  ->  qt= 3 rt=-1
 *     a= 7 b=-2:  qe=-3 re=1  ->  unchanged       (7/-2 truncates to -3)
 *
 *   FLOORING (Python `//`) rounds toward -infinity, so its remainder takes the
 *   sign of b. For b > 0 that is the Euclidean remainder already; it differs
 *   exactly when b < 0 and re != 0: qf = qe - 1, rf = re + b.
 *
 *     a= 7 b=-2:  qe=-3 re=1  ->  qf=-4 rf=-1
 *     a=-7 b=-2:  qe= 4 re=1  ->  qf= 3 rf=-1
 *     a=-7 b= 2:  qe=-4 re=1  ->  unchanged
 *
 * Division by zero is left exactly where SMT-LIB leaves it. `(div a 0)` is an
 * uninterpreted total function, and the conditions above are built on top of
 * it, so a zero divisor stays unconstrained here instead of acquiring a value
 * this lowering invented. A frontend whose language says something else about
 * it -- MiniZinc makes the enclosing context false, C calls it undefined --
 * states that as an EncodingChoice; it is not this function's to decide.
 */
std::shared_ptr<DAGNode> HirToParser::lowerCorrectedDivision(
    H::Op op, const std::shared_ptr<DAGNode>& a, const std::shared_ptr<DAGNode>& b) {
    const auto zero = parser_->mkConstInt(0);
    const auto one  = parser_->mkConstInt(1);
    const auto qe = parser_->mkDivInt(a, b);
    const auto re = parser_->mkMod(a, b);
    const auto re_nonzero = parser_->mkNot(parser_->mkEq(re, zero));
    const auto b_positive = parser_->mkGt(b, zero);

    const bool trunc = (op == H::Op::DIV_TRUNC || op == H::Op::MOD_TRUNC);
    // The condition under which the convention differs from Euclidean at all.
    const auto differs = parser_->mkAnd(
        {re_nonzero, trunc ? parser_->mkLt(a, zero) : parser_->mkLt(b, zero)});

    switch (op) {
    case H::Op::DIV_TRUNC: {
        // qe + sign(b)
        const auto step = parser_->mkIte(b_positive, one, parser_->mkConstInt(-1));
        return parser_->mkIte(differs, parser_->mkAdd({qe, step}), qe);
    }
    case H::Op::MOD_TRUNC: {
        // re - |b|
        const auto abs_b = parser_->mkIte(b_positive, b, parser_->mkNeg(b));
        return parser_->mkIte(differs, parser_->mkSub(re, abs_b), re);
    }
    case H::Op::DIV_FLOOR:
        return parser_->mkIte(differs, parser_->mkSub(qe, one), qe);
    case H::Op::MOD_FLOOR:
        return parser_->mkIte(differs, parser_->mkAdd({re, b}), re);
    default:
        // Unreachable: the caller dispatches on exactly these four. condAssert
        // rather than a silent nullptr, which would surface as "expression
        // could not be lowered" a long way from the cause.
        condAssert(false, "lowerCorrectedDivision: not a corrected division op");
        return nullptr;
    }
}

std::shared_ptr<Sort> HirToParser::lowerSort(const H::Sort& s,
                                             Uir::Diagnostics& diagnostics) {
    // Child rules only read this root's postorder cache, never re-enter the
    // traversal. A fresh cache also separates datatype-parameter environments.
    sort_cache_.clear();
    struct Frame { const H::Sort* sort; bool done; };
    std::vector<Frame> pending{{&s, false}};
    std::unordered_set<const H::Sort*> active;
    while (!pending.empty()) {
        const auto frame = pending.back();
        pending.pop_back();
        if (sort_cache_.count(frame.sort)) { continue; }
        if (!frame.done) {
            if (!active.insert(frame.sort).second) {
                diagnostics.error(ErrorCode::E_INTERNAL, "cyclic HIR sort reached lowering");
                return nullptr;
            }
            pending.push_back({frame.sort, true});
            const auto& sort = *frame.sort;
            if (sort.kind == H::SortKind::TUPLE || sort.kind == H::SortKind::DATATYPE
                || (sort.kind == H::SortKind::UNINTERPRETED && !dt_params_in_scope_.count(sort.name))) {
                for (auto it = sort.args.rbegin(); it != sort.args.rend(); ++it) {
                    if (*it) { pending.push_back({it->get(), false}); }
                }
            }
            if ((sort.kind == H::SortKind::ARRAY || sort.kind == H::SortKind::SET) && sort.elem) {
                pending.push_back({sort.elem.get(), false});
            }
            if (sort.kind == H::SortKind::ARRAY && sort.index) {
                pending.push_back({sort.index.get(), false});
            }
            continue;
        }
        auto result = lowerSortUncached(*frame.sort, diagnostics);
        if (!result) { return nullptr; }
        sort_cache_.emplace(frame.sort, std::move(result));
        active.erase(frame.sort);
    }
    return sort_cache_.at(&s);
}

std::shared_ptr<Sort> HirToParser::loweredSortOperand(const H::Sort& s,
                                                     Uir::Diagnostics& diagnostics) const {
    const auto cached = sort_cache_.find(&s);
    if (cached != sort_cache_.end()) { return cached->second; }
    diagnostics.error(ErrorCode::E_INTERNAL, "sort operand missing from lowering worklist");
    return nullptr;
}

std::shared_ptr<Sort> HirToParser::lowerSortUncached(const H::Sort& s,
                                                     Uir::Diagnostics& diagnostics) {
    switch (s.kind) {
    case H::SortKind::BOOL: return parser_->mkBoolSort();
    case H::SortKind::INT:  return parser_->mkIntSort();
    case H::SortKind::REAL: return parser_->mkRealSort();
    case H::SortKind::BITVEC:
        if (s.width == 0) {
            diagnostics.error(ErrorCode::E_INTERNAL, "a bit-vector sort has width 0");
            return nullptr;
        }
        return parser_->mkBVSort(s.width);
    case H::SortKind::FLOAT:
        return parser_->mkFPSort(s.exponent_bits, s.significand_bits);
    case H::SortKind::STRING:
        return parser_->mkStrSort();
    case H::SortKind::ROUNDING_MODE:
        return parser_->mkRoundingModeSort();
    case H::SortKind::REGLAN:
        return parser_->mkRegSort();
    case H::SortKind::SET: {
        if (!s.elem) {
            diagnostics.error(ErrorCode::E_INTERNAL, "a set sort has no element sort");
            return nullptr;
        }
        auto elem = loweredSortOperand(*s.elem, diagnostics);
        if (!elem) { return nullptr; }
        return parser_->mkSetSort(elem);
    }
    case H::SortKind::TUPLE: {
        // CREATED, not resolved -- the opposite of the datatype case below.
        // A tuple sort is structural: it is never declared by a script, it is
        // written where it is used, and `(Tuple Int Bool)` means the same
        // thing in two files that never heard of each other. The engine's
        // SortManager interns it, so two occurrences are one sort object.
        std::vector<std::shared_ptr<Sort>> fields;
        fields.reserve(s.args.size());
        for (const auto& f : s.args) {
            if (!f) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "a tuple sort has a null field");
                return nullptr;
            }
            auto lowered = loweredSortOperand(*f, diagnostics);
            if (!lowered) { return nullptr; }
            fields.push_back(std::move(lowered));
        }
        // An empty field list is UnitTuple and is correct here; createTupleSort
        // is what the engine's own parseSort calls for that spelling.
        return parser_->getSortManager()->createTupleSort(fields);
    }
    case H::SortKind::DATATYPE: {
        // Resolved rather than created: the declaration pass in lower() has
        // already registered it, and creating a second sort of the same name
        // here would give two Sort objects the engine treats as unrelated.
        auto resolved = parser_->getSymbolManager()->resolveSort(s.name);
        if (!resolved) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "datatype '" + s.name + "' is not declared");
            return nullptr;
        }
        // A PARAMETRIC datatype's application carries its arguments, and the
        // registered sort is the unapplied constructor. Instantiating here is
        // what parseSort does for a script; without it every instance lowered
        // to the same sort and `(L Int)` came out as `L`.
        if (!s.args.empty()) {
            auto applied = std::make_shared<Sort>(*resolved);
            applied->children.clear();
            for (const auto& a : s.args) {
                if (!a) { return nullptr; }
                auto la = loweredSortOperand(*a, diagnostics);
                if (!la) { return nullptr; }
                applied->children.push_back(std::move(la));
            }
            return applied;
        }
        return resolved;
    }
    case H::SortKind::UNINTERPRETED: {
        if (s.name.empty()) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "an uninterpreted sort has no name");
            return nullptr;
        }
        // A `par`-bound sort parameter is NOT a declared sort. It reaches here
        // because the lift carries it as an uninterpreted sort of arity 0 --
        // which is what it is inside the body -- and declaring it would emit
        // `(declare-sort X 0)` beside the `par (X)` that binds it: a name both
        // globally declared and locally bound, which is not a conforming
        // script. Created without registering, so it resolves for the selector
        // and appears in no declaration.
        if (dt_params_in_scope_.count(s.name) != 0) {
            return parser_->getSortManager()->createSort(
                SORT_KIND::SK_DEC, s.name, 0);
        }
        // The arity is the number of arguments, so `(declare-sort S 1)` is
        // emitted by the same call that emits `(declare-sort U 0)`.
        auto ctor = parser_->mkSortDec(s.name, s.args.size());
        if (!ctor) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "could not declare sort '" + s.name + "'");
            return nullptr;
        }
        if (s.args.empty()) { return ctor; }
        // An APPLICATION is a distinct sort value carrying its arguments.
        // mkSortApp clones the constructor rather than filling it, so two
        // instantiations stay two sorts; handing back `ctor` for each is how
        // `(S Bool)` and `(S Int)` became one.
        std::vector<std::shared_ptr<Sort>> args;
        args.reserve(s.args.size());
        for (const auto& a : s.args) {
            if (!a) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "sort '" + s.name + "' has a null argument");
                return nullptr;
            }
            auto lowered = loweredSortOperand(*a, diagnostics);
            if (!lowered) { return nullptr; }
            args.push_back(std::move(lowered));
        }
        auto applied = parser_->mkSortApp(ctor, args);
        if (!applied || applied->isNull()) {
            // mkSortApp returns the null sort rather than throwing, so the
            // arity disagreement is reported here with the name in it.
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "sort '" + s.name + "' could not be applied to "
                                  + std::to_string(args.size()) + " argument(s)");
            return nullptr;
        }
        return applied;
    }
    case H::SortKind::ARRAY: {
        if (!s.index || !s.elem) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "an array sort is missing its index or element sort");
            return nullptr;
        }
        auto i = loweredSortOperand(*s.index, diagnostics);
        auto v = loweredSortOperand(*s.elem, diagnostics);
        if (!i || !v) { return nullptr; }
        return parser_->mkArraySort(i, v);
    }
    }
    diagnostics.error(ErrorCode::E_INTERNAL, "unhandled HIR sort kind");
    return nullptr;
}

std::shared_ptr<DAGNode> HirToParser::lowerExpr(const H::ExprPtr& e,
                                                Uir::Diagnostics& diagnostics) {
    if (lower_expr_depth_ == 0) {
        Detail::clearExpressionRootCache(expr_cache_);
        lower_scope_epoch_ = ++next_lower_scope_epoch_;
    }
    if (e) {
        const auto cached = expr_cache_.find({e.get(), lower_scope_epoch_});
        if (cached != expr_cache_.end()) { return cached->second; }
    }
    struct DepthGuard {
        std::size_t& depth;
        explicit DepthGuard(std::size_t& d) : depth(d) { ++depth; }
        ~DepthGuard() { --depth; }
    } depth_guard(lower_expr_depth_);

    // Both operand traversal and quantifier scope entry/exit use this worklist.
    struct QuantifierScope {
        std::size_t enclosing_scope;
        std::vector<std::pair<std::string, std::shared_ptr<DAGNode>>> previous;
        std::vector<std::shared_ptr<DAGNode>> params{nullptr};
    };
    struct Pending {
        const H::ExprPtr* expression;
        std::size_t next_argument = 0;
        std::unique_ptr<QuantifierScope> quantifier{};
    };
    std::vector<Pending> pending;
    pending.push_back({&e});
    const auto leave_scope = [&](Pending& frame) {
        if (!frame.quantifier) { return; }
        for (auto it = frame.quantifier->previous.rbegin(); it != frame.quantifier->previous.rend(); ++it) {
            if (it->second) { bound_[it->first] = it->second; }
            else { bound_.erase(it->first); }
        }
        lower_scope_epoch_ = frame.quantifier->enclosing_scope;
        frame.quantifier.reset();
    };
    const auto fail = [&]() -> std::shared_ptr<DAGNode> {
        while (!pending.empty()) { leave_scope(pending.back()); pending.pop_back(); }
        return nullptr;
    };
    std::unordered_set<const H::Expr*> active;
    if (e) { active.insert(e.get()); }
    std::shared_ptr<DAGNode> result;
    while (!pending.empty()) {
        auto& frame = pending.back();
        const auto& expression = *frame.expression;
        const bool quantified = expression && (expression->kind == H::ExprKind::FORALL
            || expression->kind == H::ExprKind::EXISTS);
        if (quantified && !frame.quantifier) {
            if (expression->binders.empty() || expression->args.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL, "a quantifier reached lowering malformed", expression->loc);
                return fail();
            }
            frame.quantifier = std::make_unique<QuantifierScope>();
            frame.quantifier->enclosing_scope = lower_scope_epoch_;
            for (const auto& binder : expression->binders) {
                auto sort = lowerSort(binder.sort, diagnostics);
                if (!sort) { return fail(); }
                auto variable = parser_->mkQuantVar(emitName(binder.name, diagnostics), sort);
                if (!variable) {
                    diagnostics.error(ErrorCode::E_INTERNAL,
                        "could not create quantified variable '" + binder.name + "'", expression->loc);
                    return fail();
                }
                const auto previous = bound_.find(binder.name);
                frame.quantifier->previous.emplace_back(binder.name,
                    previous == bound_.end() ? nullptr : previous->second);
                bound_[binder.name] = variable;
                frame.quantifier->params.push_back(variable);
            }
            lower_scope_epoch_ = ++next_lower_scope_epoch_;
        }
        const bool ordinary = expression && (expression->kind == H::ExprKind::OP
            || expression->kind == H::ExprKind::APPLY
            || expression->kind == H::ExprKind::DT_CONSTRUCTOR
            || expression->kind == H::ExprKind::DT_SELECTOR
            || expression->kind == H::ExprKind::DT_TESTER);
        if ((ordinary || quantified) && frame.next_argument < expression->args.size()) {
            const auto& child = expression->args[frame.next_argument++];
            if (child) {
                if (expr_cache_.count({child.get(), lower_scope_epoch_})) { continue; }
                if (!active.insert(child.get()).second) {
                    diagnostics.error(ErrorCode::E_INTERNAL,
                                      "cyclic HIR expression reached lowering", expression->loc);
                    return fail();
                }
            }
            pending.push_back({&child});
            continue;
        }
        if (quantified) {
            auto params = std::move(frame.quantifier->params);
            const auto body = expr_cache_.find({expression->args[0].get(), lower_scope_epoch_});
            if (body == expr_cache_.end()) {
                diagnostics.error(ErrorCode::E_INTERNAL, "quantifier body missing from lowering worklist", expression->loc);
                return fail();
            }
            params[0] = body->second;
            leave_scope(frame);
            result = expression->kind == H::ExprKind::FORALL ? parser_->mkForall(params) : parser_->mkExists(params);
        } else {
            result = lowerExprUncached(expression, diagnostics);
        }
        if (!result) { return fail(); }
        if (expression) {
            expr_cache_[{expression.get(), lower_scope_epoch_}] = result;
            active.erase(expression.get());
        }
        pending.pop_back();
    }
    return result;
}

std::shared_ptr<DAGNode> HirToParser::loweredOperand(const H::ExprPtr& e,
                                                   Uir::Diagnostics& diagnostics) const {
    const auto cached = expr_cache_.find({e.get(), lower_scope_epoch_});
    if (cached != expr_cache_.end()) { return cached->second; }
    // Local operator rules must not start a second traversal. In particular,
    // a shared child visited under an inner binder must not evict its outer
    // scope result and silently trigger depth-dependent recursive lowering.
    diagnostics.error(ErrorCode::E_INTERNAL, "expression operand missing from lowering worklist",
                      e ? e->loc : Uir::SourceLoc{});
    return nullptr;
}

std::shared_ptr<DAGNode> HirToParser::lowerExprUncached(const H::ExprPtr& e,
                                                       Uir::Diagnostics& diagnostics) {
    if (!e) {
        diagnostics.error(ErrorCode::E_INTERNAL, "null HIR expression reached lowering");
        return nullptr;
    }

    switch (e->kind) {
    case H::ExprKind::LIT_BOOL:
        return e->bool_value ? parser_->mkTrue() : parser_->mkFalse();

    case H::ExprKind::LIT_INT:
        // The NAME, not int_value: an OPB coefficient may exceed LLONG_MAX and
        // the engine's Number is GMP-backed, so the magnitude survives the whole
        // way down provided nothing in between narrows it to a machine integer.
        return parser_->mkConstInt(e->name.empty() ? std::to_string(e->int_value)
                                                   : e->name);

    case H::ExprKind::BOUND_VAR: {
        // Bound variables live in their own scope, pushed by the enclosing
        // quantifier. Looking them up in vars_ -- the model's free variables --
        // would either miss them or, worse, find an unrelated model variable of
        // the same name. typeCheck rejects that shadowing, so a miss here is a
        // broken invariant rather than a bad input.
        const auto it = bound_.find(e->name);
        if (it == bound_.end()) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "bound variable '" + e->name
                                  + "' reached lowering with no binder in scope",
                              e->loc);
            return nullptr;
        }
        return it->second;
    }

    case H::ExprKind::FORALL:
    case H::ExprKind::EXISTS:
        diagnostics.error(ErrorCode::E_INTERNAL, "quantifier bypassed scoped lowering worklist", e->loc);
        return nullptr;

    case H::ExprKind::LIT_BITVEC:
        return parser_->mkConstBv(e->name, e->sort.width);

    case H::ExprKind::LIT_REAL:
        return parser_->mkConstReal(e->name);

    case H::ExprKind::LIT_FLOAT:
        return parser_->mkConstFp(e->name, e->sort.exponent_bits,
                                  e->sort.significand_bits);

    case H::ExprKind::DT_CONSTRUCTOR:
    case H::ExprKind::DT_SELECTOR:
    case H::ExprKind::DT_TESTER: {
        auto result = lowerSort(e->sort, diagnostics);
        if (!result) { return nullptr; }
        std::vector<std::shared_ptr<DAGNode>> args;
        args.reserve(e->args.size());
        for (const auto& a : e->args) {
            auto n = loweredOperand(a, diagnostics);
            if (!n) { return nullptr; }
            args.push_back(std::move(n));
        }
        // mkApplyUF plus getDtFunctionKind is the engine's own route: it looks
        // the name up in the datatype tables and picks NT_DT_CONSTRUCTOR,
        // NT_DT_SELECTOR or NT_DT_TESTER. Building the node kind here instead
        // would duplicate a decision the engine already makes, and the two
        // copies would drift.
        if (e->kind == H::ExprKind::DT_TESTER) {
            // A tester's *name* in the engine is the "is-<ctor>" spelling; the
            // HIR carries the bare constructor name, because that is what the
            // source formats write.
            return parser_->mkApplyUF(result, "is-" + e->name, args);
        }
        return parser_->mkApplyUF(result, e->name, args);
    }

    case H::ExprKind::LIT_SET: {
        auto sort = lowerSort(e->sort, diagnostics);
        if (!sort) { return nullptr; }
        return e->name == "set.empty" ? parser_->mkSetEmpty(sort)
                                      : parser_->mkSetUniverse(sort);
    }

    case H::ExprKind::LIT_TUPLE_UNIT:
        // `mkTuple({})` and not a hand-built node: the engine's builder is
        // what decides that the nullary case is NT_TUPLE_UNIT rather than an
        // empty NT_TUPLE_CONSTRUCTOR, and that decision must be made in one
        // place (HirToParser makes no decisions -- CLAUDE.md §4.2).
        return parser_->mkTuple({});

    case H::ExprKind::LIT_REGLAN:
        if (e->name == "re.none")    { return parser_->mkRegNone(); }
        if (e->name == "re.all")     { return parser_->mkRegAll(); }
        if (e->name == "re.allchar") { return parser_->mkRegAllChar(); }
        diagnostics.error(ErrorCode::E_INTERNAL,
                          "unknown regular-expression constant '" + e->name + "'",
                          e->loc);
        return nullptr;

    case H::ExprKind::LIT_ROUNDING_MODE:
        // The engine takes the mode by name; Uir::Hir::typeCheck has already
        // refused anything that is not one of SMT-LIB's five, so an unknown
        // name cannot reach the script from here.
        return parser_->mkRoundingMode(e->name);

    case H::ExprKind::LIT_STRING:
        return parser_->mkConstStr(e->name);

    case H::ExprKind::APPLY: {
        std::vector<std::shared_ptr<DAGNode>> args;
        args.reserve(e->args.size());
        for (const auto& a : e->args) {
            auto n = loweredOperand(a, diagnostics);
            if (!n) { return nullptr; }
            args.push_back(std::move(n));
        }
        auto result = lowerSort(e->sort, diagnostics);
        if (!result) { return nullptr; }
        return parser_->mkApplyUF(result, emitName(e->name, diagnostics), args);
    }

    case H::ExprKind::GLOBAL:
        // decompose-globals runs before lowering and replaces every one of
        // these. Reaching here means the profile did not run it, and emitting
        // anything at all would be inventing a meaning for a constraint we
        // deliberately do not have a default encoding for.
        diagnostics.error(ErrorCode::E_INTERNAL,
                          "global constraint '" + e->name
                              + "' reached lowering; no decomposition pass ran",
                          e->loc);
        return nullptr;

    case H::ExprKind::IDENT: {
        const auto it = vars_.find(e->name);
        if (it == vars_.end()) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "undeclared identifier '" + e->name + "' reached lowering",
                              e->loc);
            return nullptr;
        }
        return it->second;
    }

    case H::ExprKind::OP: {
        if (e->op == H::Op::CONST_ARRAY) {
            // `((as const (Array T U)) v)` -- built from the SORT and the
            // value, because the sort is where the array's identity lives:
            // the value fixes U and says nothing about T.
            if (e->args.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "a constant array takes one value", e->loc);
                return nullptr;
            }
            auto sort = lowerSort(e->sort, diagnostics);
            if (!sort) { return nullptr; }
            auto v = loweredOperand(e->args[0], diagnostics);
            if (!v) { return nullptr; }
            return parser_->mkConstArray(sort, v);
        }
        std::vector<std::shared_ptr<DAGNode>> args;
        args.reserve(e->args.size());
        for (const auto& a : e->args) {
            auto n = loweredOperand(a, diagnostics);
            if (!n) {
                return nullptr;
            }
            args.push_back(std::move(n));
        }
        switch (e->op) {
        case H::Op::AND: return parser_->mkAnd(args);
        case H::Op::OR:  return parser_->mkOr(args);
        case H::Op::NOT:
            if (args.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL, "not/1 got wrong arity", e->loc);
                return nullptr;
            }
            return parser_->mkNot(args[0]);
        case H::Op::XOR: return parser_->mkXor(args);
        case H::Op::DISTINCT: return parser_->mkDistinct(args);
        case H::Op::IMPLIES:
            if (args.size() != 2) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "=> expects two arguments", e->loc);
                return nullptr;
            }
            return parser_->mkImplies(args[0], args[1]);
        case H::Op::NEG:
        case H::Op::ABS:
            if (args.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects one argument",
                                  e->loc);
                return nullptr;
            }
            return e->op == H::Op::NEG ? parser_->mkNeg(args[0]) : parser_->mkAbs(args[0]);
        case H::Op::ITE:
            if (args.size() != 3) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "ite expects a condition and two branches", e->loc);
                return nullptr;
            }
            return parser_->mkIte(args[0], args[1], args[2]);
        case H::Op::ADD: return parser_->mkAdd(args);
        case H::Op::MUL: return parser_->mkMul(args);
        case H::Op::ARRAY_MAP_AND: return parser_->mkArrayMap("and", args);
        case H::Op::ARRAY_MAP_OR: return parser_->mkArrayMap("or", args);
        case H::Op::ARRAY_MAP_NOT: return parser_->mkArrayMap("not", args);
        case H::Op::SELECT:
            if (args.size() != 2) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "select expects an array and an index", e->loc);
                return nullptr;
            }
            return parser_->mkSelect(args[0], args[1]);
        case H::Op::STORE:
            if (args.size() != 3) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "store expects an array, an index and a value",
                                  e->loc);
                return nullptr;
            }
            return parser_->mkStore(args[0], args[1], args[2]);
        case H::Op::EQ:
            if (args.size() < 2) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "= expects at least two arguments", e->loc);
                return nullptr;
            }
            return parser_->mkEq(args);
        case H::Op::LE:
        case H::Op::LT:
        case H::Op::GE:
        case H::Op::GT:
            if (args.size() < 2) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects at least two arguments",
                                  e->loc);
                return nullptr;
            }
            // Ordered chains relate adjacent operands: lo <= x <= hi.
            // Keep the shared HIR compact and let the native builder lower it.
            switch (e->op) {
            case H::Op::LE: return parser_->mkLe(args);
            case H::Op::LT: return parser_->mkLt(args);
            case H::Op::GE: return parser_->mkGe(args);
            case H::Op::GT: return parser_->mkGt(args);
            default: return nullptr;
            }
        case H::Op::SUB:
        case H::Op::DIV_REAL:
        case H::Op::DIV_EUCLID:
        case H::Op::MOD_EUCLID:
        case H::Op::DIV_TRUNC:
        case H::Op::MOD_TRUNC:
        case H::Op::DIV_FLOOR:
        case H::Op::MOD_FLOOR:
            if (args.size() != 2) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects two arguments",
                                  e->loc);
                return nullptr;
            }
            switch (e->op) {
            case H::Op::SUB: return parser_->mkSub(args[0], args[1]);
            case H::Op::DIV_REAL: return parser_->mkDivReal(args[0], args[1]);
            // SMT-LIB's div/mod ARE the Euclidean pair, so these lower with no
            // correction at all. That is the reason Euclidean is worth having
            // as its own Op rather than being expressed through one of the
            // others: the common case emits exactly what the source said.
            case H::Op::DIV_EUCLID: return parser_->mkDivInt(args[0], args[1]);
            case H::Op::MOD_EUCLID: return parser_->mkMod(args[0], args[1]);
            case H::Op::DIV_TRUNC:
            case H::Op::MOD_TRUNC:
            case H::Op::DIV_FLOOR:
            case H::Op::MOD_FLOOR:
                return lowerCorrectedDivision(e->op, args[0], args[1]);
            default:         return nullptr;
            }
        default:
            // Other theories are dispatched by the handlers below.
            break;
        }

        // ---- Bit-vectors ---------------------------------------------------
        // Every arity has already been checked by Uir::Hir::typeCheck, so the
        // guards below are for expressions built by hand and handed straight to
        // lowering. They report rather than abort because the Parser builders
        // throw, and translate()'s contract is a recorded failure per benchmark
        // (translation/diagnostic.h) rather than an escaped exception.
        if (isBitVecOp(e->op)) {
            const auto wrongArity = [&](const char* want) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects " + want,
                                  e->loc);
                return std::shared_ptr<DAGNode>(nullptr);
            };
            switch (e->op) {
            // n-ary in SMT-LIB and n-ary here.
            case H::Op::BV_AND: return parser_->mkBvAnd(args);
            case H::Op::BV_OR:  return parser_->mkBvOr(args);
            case H::Op::BV_XOR: return parser_->mkBvXor(args);
            case H::Op::BV_ADD: return parser_->mkBvAdd(args);
            case H::Op::BV_MUL: return parser_->mkBvMul(args);
            case H::Op::BV_CONCAT: return parser_->mkBvConcat(args);
            default: break;
            }
            if (e->op == H::Op::BV_NOT || e->op == H::Op::BV_NEG) {
                if (args.size() != 1) { return wrongArity("one argument"); }
                return e->op == H::Op::BV_NOT ? parser_->mkBvNot(args[0])
                                              : parser_->mkBvNeg(args[0]);
            }
            if (e->op == H::Op::BV_EXTRACT) {
                if (args.size() != 1 || e->indices.size() != 2) {
                    return wrongArity("one argument and two indices");
                }
                // The engine takes the indices as constant nodes rather than as
                // integers, which is how (_ extract hi lo) is spelled once it
                // is a DAG: the indices are part of the operator, so they are
                // children of the extract node.
                return parser_->mkBvExtract(
                    args[0],
                    parser_->mkConstInt(static_cast<int>(e->indices[0])),
                    parser_->mkConstInt(static_cast<int>(e->indices[1])));
            }
            if (e->op == H::Op::BV_ZERO_EXTEND || e->op == H::Op::BV_SIGN_EXTEND) {
                if (args.size() != 1 || e->indices.size() != 1) {
                    return wrongArity("one argument and one index");
                }
                auto by = parser_->mkConstInt(static_cast<int>(e->indices[0]));
                return e->op == H::Op::BV_ZERO_EXTEND
                           ? parser_->mkBvZeroExt(args[0], by)
                           : parser_->mkBvSignExt(args[0], by);
            }
            if (e->op == H::Op::BV_ROTATE_LEFT || e->op == H::Op::BV_ROTATE_RIGHT
                || e->op == H::Op::BV_REPEAT) {
                if (args.size() != 1 || e->indices.size() != 1) {
                    return wrongArity("one argument and one index");
                }
                auto n = parser_->mkConstInt(static_cast<int>(e->indices[0]));
                switch (e->op) {
                case H::Op::BV_ROTATE_LEFT:  return parser_->mkBvRotateLeft(args[0], n);
                case H::Op::BV_ROTATE_RIGHT: return parser_->mkBvRotateRight(args[0], n);
                default:                     return parser_->mkBvRepeat(args[0], n);
                }
            }
            if (args.size() != 2) { return wrongArity("two arguments"); }
            switch (e->op) {
            case H::Op::BV_NAND: return parser_->mkBvNand(args[0], args[1]);
            case H::Op::BV_NOR:  return parser_->mkBvNor(args[0], args[1]);
            case H::Op::BV_XNOR: return parser_->mkBvXnor(args[0], args[1]);
            case H::Op::BV_SUB:  return parser_->mkBvSub(args[0], args[1]);
            case H::Op::BV_UDIV: return parser_->mkBvUdiv(args[0], args[1]);
            case H::Op::BV_UREM: return parser_->mkBvUrem(args[0], args[1]);
            case H::Op::BV_SDIV: return parser_->mkBvSdiv(args[0], args[1]);
            case H::Op::BV_SREM: return parser_->mkBvSrem(args[0], args[1]);
            case H::Op::BV_SMOD: return parser_->mkBvSmod(args[0], args[1]);
            case H::Op::BV_SHL:  return parser_->mkBvShl(args[0], args[1]);
            case H::Op::BV_LSHR: return parser_->mkBvLshr(args[0], args[1]);
            case H::Op::BV_ASHR: return parser_->mkBvAshr(args[0], args[1]);
            case H::Op::BV_ULT:  return parser_->mkBvUlt(args[0], args[1]);
            case H::Op::BV_ULE:  return parser_->mkBvUle(args[0], args[1]);
            case H::Op::BV_UGT:  return parser_->mkBvUgt(args[0], args[1]);
            case H::Op::BV_UGE:  return parser_->mkBvUge(args[0], args[1]);
            case H::Op::BV_SLT:  return parser_->mkBvSlt(args[0], args[1]);
            case H::Op::BV_SLE:  return parser_->mkBvSle(args[0], args[1]);
            case H::Op::BV_SGT:  return parser_->mkBvSgt(args[0], args[1]);
            case H::Op::BV_SGE:  return parser_->mkBvSge(args[0], args[1]);
            case H::Op::BV_COMP: return parser_->mkBvComp(args[0], args[1]);
            default: break;
            }
        }
        // ---- Floating point -------------------------------------------------
        // The rounding mode is the first argument, which is what SortKind
        // ROUNDING_MODE exists for; the engine's n-ary builders take it in the
        // same position, so the vector is passed through unchanged.
        if (H::isFloatOp(e->op)) {
            const auto wrongArity = [&](const char* want) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects " + want,
                                  e->loc);
                return std::shared_ptr<DAGNode>(nullptr);
            };
            switch (e->op) {
            case H::Op::FP_ADD: return parser_->mkFpAdd(args);
            case H::Op::FP_SUB: return parser_->mkFpSub(args);
            case H::Op::FP_MUL: return parser_->mkFpMul(args);
            case H::Op::FP_DIV: return parser_->mkFpDiv(args);
            case H::Op::FP_FMA: return parser_->mkFpFma(args);
            default: break;
            }
            if (e->op == H::Op::FP_SQRT || e->op == H::Op::FP_ROUND_TO_INTEGRAL) {
                if (args.size() != 2) { return wrongArity("a rounding mode and a value"); }
                return e->op == H::Op::FP_SQRT
                           ? parser_->mkFpSqrt(args[0], args[1])
                           : parser_->mkFpRoundToIntegral(args[0], args[1]);
            }
            if (args.size() == 1) {
                switch (e->op) {
                case H::Op::FP_ABS: return parser_->mkFpAbs(args[0]);
                case H::Op::FP_NEG: return parser_->mkFpNeg(args[0]);
                case H::Op::FP_IS_NORMAL:    return parser_->mkFpIsNormal(args[0]);
                case H::Op::FP_IS_SUBNORMAL: return parser_->mkFpIsSubnormal(args[0]);
                case H::Op::FP_IS_ZERO:      return parser_->mkFpIsZero(args[0]);
                case H::Op::FP_IS_INFINITE:  return parser_->mkFpIsInf(args[0]);
                case H::Op::FP_IS_NAN:       return parser_->mkFpIsNaN(args[0]);
                case H::Op::FP_IS_NEGATIVE:  return parser_->mkFpIsNeg(args[0]);
                case H::Op::FP_IS_POSITIVE:  return parser_->mkFpIsPos(args[0]);
                default: break;
                }
                return wrongArity("more than one argument");
            }
            if (args.size() != 2) { return wrongArity("two arguments"); }
            switch (e->op) {
            case H::Op::FP_REM: return parser_->mkFpRem(args[0], args[1]);
            // n-ary in the engine even though SMT-LIB's fp.min/fp.max are binary.
            case H::Op::FP_MIN: return parser_->mkFpMin(args);
            case H::Op::FP_MAX: return parser_->mkFpMax(args);
            case H::Op::FP_LEQ: return parser_->mkFpLe(args[0], args[1]);
            case H::Op::FP_LT:  return parser_->mkFpLt(args[0], args[1]);
            case H::Op::FP_GEQ: return parser_->mkFpGe(args[0], args[1]);
            case H::Op::FP_GT:  return parser_->mkFpGt(args[0], args[1]);
            // mkFpEq, not mkEq. fp.eq is IEEE equality -- NaN equals nothing,
            // +0 equals -0 -- and SMT-LIB's = on Float is structural, which
            // disagrees on exactly those values. Routing this through mkEq
            // would type-check, lower, and answer a different question.
            case H::Op::FP_EQ:  return parser_->mkFpEq(args[0], args[1]);
            default: break;
            }
        }

        // ---- Strings --------------------------------------------------------
        if (H::isStringOp(e->op)) {
            const auto wrongArity = [&](const char* want) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects " + want,
                                  e->loc);
                return std::shared_ptr<DAGNode>(nullptr);
            };
            if (e->op == H::Op::STR_CONCAT) { return parser_->mkStrConcat(args); }
            if (args.size() == 1) {
                switch (e->op) {
                case H::Op::STR_LEN:      return parser_->mkStrLen(args[0]);
                case H::Op::STR_TO_INT:   return parser_->mkStrToInt(args[0]);
                case H::Op::STR_FROM_INT: return parser_->mkStrFromInt(args[0]);
                // isStringOp covers these, so they reach this block and not the
                // regular-expression one below.
                case H::Op::STR_TO_CODE:   return parser_->mkStrToCode(args[0]);
                case H::Op::STR_FROM_CODE: return parser_->mkStrFromCode(args[0]);
                case H::Op::STR_IS_DIGIT:  return parser_->mkStrIsDigit(args[0]);
                default: break;
                }
                return wrongArity("more than one argument");
            }
            if (args.size() == 2) {
                switch (e->op) {
                case H::Op::STR_AT:       return parser_->mkStrCharat(args[0], args[1]);
                case H::Op::STR_CONTAINS: return parser_->mkStrContains(args[0], args[1]);
                case H::Op::STR_PREFIXOF: return parser_->mkStrPrefixof(args[0], args[1]);
                case H::Op::STR_SUFFIXOF: return parser_->mkStrSuffixof(args[0], args[1]);
                case H::Op::STR_LT:       return parser_->mkStrLt(args[0], args[1]);
                case H::Op::STR_LE:       return parser_->mkStrLe(args[0], args[1]);
                default: break;
                }
                return wrongArity("three arguments");
            }
            if (args.size() != 3) { return wrongArity("three arguments"); }
            switch (e->op) {
            case H::Op::STR_INDEXOF_RE:  return parser_->mkStrIndexofReg(args[0], args[1], args[2]);
            case H::Op::STR_REPLACE_RE:  return parser_->mkStrReplaceReg(args[0], args[1], args[2]);
            case H::Op::STR_REPLACE_RE_ALL: return parser_->mkStrReplaceRegAll(args[0], args[1], args[2]);
            case H::Op::STR_SUBSTR:      return parser_->mkStrSubstr(args[0], args[1], args[2]);
            case H::Op::STR_INDEXOF:     return parser_->mkStrIndexof(args[0], args[1], args[2]);
            case H::Op::STR_REPLACE:     return parser_->mkStrReplace(args[0], args[1], args[2]);
            case H::Op::STR_REPLACE_ALL: return parser_->mkStrReplaceAll(args[0], args[1], args[2]);
            default: break;
            }
        }

        // ---- Finite sets ----------------------------------------------------
        if (H::isSetOp(e->op)) {
            const auto wrongArity = [&](const char* want) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects " + want,
                                  e->loc);
                return std::shared_ptr<DAGNode>(nullptr);
            };
            switch (e->op) {
            case H::Op::SET_UNION:  return parser_->mkSetUnion(args);
            case H::Op::SET_INTER:  return parser_->mkSetInter(args);
            case H::Op::SET_INSERT: return parser_->mkSetInsert(args);
            default: break;
            }
            if (args.size() == 1) {
                switch (e->op) {
                case H::Op::SET_SINGLETON:  return parser_->mkSetSingleton(args[0]);
                case H::Op::SET_CARD:       return parser_->mkSetCard(args[0]);
                case H::Op::SET_COMPLEMENT: return parser_->mkSetComplement(args[0]);
                default: break;
                }
                return wrongArity("two arguments");
            }
            if (args.size() != 2) { return wrongArity("two arguments"); }
            switch (e->op) {
            case H::Op::SET_MINUS:  return parser_->mkSetMinus(args[0], args[1]);
            case H::Op::SET_MEMBER: return parser_->mkSetMember(args[0], args[1]);
            case H::Op::SET_SUBSET: return parser_->mkSetSubset(args[0], args[1]);
            default: break;
            }
        }

        // ---- Tuples ---------------------------------------------------------
        if (H::isTupleOp(e->op)) {
            const auto wrongShape = [&](const char* want) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects " + want,
                                  e->loc);
                return std::shared_ptr<DAGNode>(nullptr);
            };
            if (e->op == H::Op::TUPLE) {
                if (args.empty()) { return wrongShape("at least one field"); }
                return parser_->mkTuple(args);
            }
            // The indices go back to being constant NODES, which is how the
            // engine spells `(_ tuple.select i)` once it is a DAG -- the same
            // conversion BV_EXTRACT makes below, and the exact inverse of what
            // ParserToHir did on the way up.
            if (args.empty()) { return wrongShape("a tuple argument"); }
            if (e->op == H::Op::TUPLE_PROJECT) {
                // Projection onto no fields is the unique unit tuple. The
                // indexed SMT spelling requires at least one index, so emit
                // the equivalent value instead of an invalid indexed symbol.
                if (e->indices.empty()) { return parser_->mkTuple({}); }
                std::vector<std::shared_ptr<DAGNode>> idx;
                idx.reserve(e->indices.size());
                for (unsigned i : e->indices) {
                    idx.push_back(parser_->mkConstInt(static_cast<int>(i)));
                }
                return parser_->mkTupleProject(args[0], idx);
            }
            if (e->indices.size() != 1) { return wrongShape("one index"); }
            auto index = parser_->mkConstInt(static_cast<int>(e->indices[0]));
            if (e->op == H::Op::TUPLE_SELECT) {
                if (args.size() != 1) { return wrongShape("one argument"); }
                return parser_->mkTupleSelect(args[0], index);
            }
            if (args.size() != 2) { return wrongShape("a tuple and a value"); }
            return parser_->mkTupleUpdate(args[0], index, args[1]);
        }

        // ---- Regular expressions and cross-theory conversions ---------------
        // `divisible` is neither a regex nor a conversion; it is here because
        // this is the block that carries the index-to-constant-node helper, and
        // it is the only arithmetic operator that needs one.
        if (H::isRegexOp(e->op) || H::isConversionOp(e->op)
            || e->op == H::Op::IS_DIVISIBLE) {
            const auto wrongArity = [&](const char* want) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  std::string(opName(e->op)) + " expects " + want,
                                  e->loc);
                return std::shared_ptr<DAGNode>(nullptr);
            };
            // The engine takes an indexed operator's indices as constant nodes,
            // the same shape as (_ extract hi lo): the indices are part of the
            // operator, so they are children of its node.
            const auto k = [&](unsigned v) {
                // Preserve the full unsigned HIR index. Narrowing through int
                // silently changed large re.loop and conversion indices.
                return parser_->mkConstInt(std::to_string(v));
            };
            switch (e->op) {
            case H::Op::RE_CONCAT: return parser_->mkRegConcat(args);
            case H::Op::RE_UNION:  return parser_->mkRegUnion(args);
            case H::Op::RE_INTER:  return parser_->mkRegInter(args);
            case H::Op::RE_DIFF:   return parser_->mkRegDiff(args);
            default: break;
            }
            if (args.size() == 1) {
                switch (e->op) {
                case H::Op::STR_TO_RE:      return parser_->mkStrToReg(args[0]);
                case H::Op::RE_STAR:        return parser_->mkRegStar(args[0]);
                case H::Op::RE_PLUS:        return parser_->mkRegPlus(args[0]);
                case H::Op::RE_OPT:         return parser_->mkRegOpt(args[0]);
                case H::Op::RE_COMPLEMENT:  return parser_->mkRegComplement(args[0]);
                case H::Op::TO_INT:         return parser_->mkToInt(args[0]);
                case H::Op::TO_REAL:        return parser_->mkToReal(args[0]);
                case H::Op::IS_INT:         return parser_->mkIsInt(args[0]);
                case H::Op::IS_DIVISIBLE:
                    if (e->indices.size() != 1) { return wrongArity("one index"); }
                    // The engine keeps the divisor as a second CHILD and prints
                    // the indexed form from it, so the index becomes an argument
                    // here rather than staying an index.
                    return parser_->mkIsDivisible(args[0], k(e->indices[0]));
                case H::Op::BV_TO_NAT:      return parser_->mkBvToNat(args[0]);
                case H::Op::BV_TO_INT:      return parser_->mkBvToInt(args[0]);
                case H::Op::FP_TO_REAL:     return parser_->mkFpToReal(args[0]);
                case H::Op::FP_TO_IEEE_BV:  return parser_->mkFpToIeeeBv(args[0]);
                case H::Op::IEEE_BV_TO_FP:
                    if (e->indices.size() != 2) {
                        return wrongArity("two indices");
                    }
                    return parser_->mkToFp(k(e->indices[0]), k(e->indices[1]),
                                           args[0]);
                case H::Op::RE_LOOP:
                    if (e->indices.size() != 2) {
                        return wrongArity("two indices");
                    }
                    return parser_->mkRegLoop(args[0], k(e->indices[0]),
                                              k(e->indices[1]));
                case H::Op::INT_TO_BV:
                    if (e->indices.size() != 1) { return wrongArity("one index"); }
                    return parser_->mkIntToBv(args[0], k(e->indices[0]));
                default: break;
                }
                return wrongArity("more than one argument");
            }
            if (args.size() != 2) { return wrongArity("two arguments"); }
            switch (e->op) {
            case H::Op::STR_IN_RE: return parser_->mkStrInReg(args[0], args[1]);
            case H::Op::RE_RANGE:  return parser_->mkRegRange(args[0], args[1]);
            case H::Op::FP_TO_SBV:
                if (e->indices.size() != 1) { return wrongArity("one index"); }
                return parser_->mkFpToSbv(args[0], args[1], k(e->indices[0]));
            case H::Op::FP_TO_UBV:
                if (e->indices.size() != 1) { return wrongArity("one index"); }
                return parser_->mkFpToUbv(args[0], args[1], k(e->indices[0]));
            case H::Op::TO_FP:
                if (e->indices.size() != 2) { return wrongArity("two indices"); }
                return parser_->mkToFp(k(e->indices[0]), k(e->indices[1]),
                                       args[0], args[1]);
            case H::Op::TO_FP_UNSIGNED:
                if (e->indices.size() != 2) { return wrongArity("two indices"); }
                return parser_->mkToFpUnsigned(k(e->indices[0]), k(e->indices[1]),
                                               args[0], args[1]);
            default: break;
            }
        }

        diagnostics.error(ErrorCode::E_INTERNAL, "unhandled HIR operator", e->loc);
        return nullptr;
    }
    }

    diagnostics.error(ErrorCode::E_INTERNAL, "unhandled HIR expression kind", e->loc);
    return nullptr;
}

const std::string& HirToParser::emitName(const std::string& hir_name,
                                         Uir::Diagnostics& diagnostics) {
    const auto memo = emit_names_.find(hir_name);
    if (memo != emit_names_.end()) { return memo->second; }
    // Quoting changes a symbol's spelling, not its identity. Constants such
    // as true/false live outside oper_key_map, but their names likewise cannot
    // be redeclared in the SMT target. Keep this source-to-target renaming
    // here rather than changing the parser's source-language shadow rules.
    std::string unquoted;
    const std::string* symbol = &hir_name;
    if (hir_name.size() >= 2 && hir_name.front() == '|' && hir_name.back() == '|') {
        unquoted = hir_name.substr(1, hir_name.size() - 2);
        symbol = &unquoted;
    }
    const auto reserved = [](const std::string& name) {
        return SOMTParser::isBuiltinNameReservedAgainstUserFun(name)
            || SOMTParser::kind_key_map.count(name) != 0;
    };
    if (!reserved(*symbol)) {
        // Identity mappings need no owned key/value pair. The caller owns
        // hir_name through this call; declarations/builders copy emitted names.
        return hir_name;
    }
    // `!` is a legal character in an SMT-LIB simple symbol and is what the
    // engine's own generated binders use (`!i0`), so a renamed symbol reads as
    // machine-made rather than as something the author wrote.
    std::string candidate;
    for (unsigned i = 0;; ++i) {
        candidate = *symbol + "!" + std::to_string(i);
        if (!containsSmtSymbol(taken_names_, candidate)
            && !reserved(candidate)) {
            break;
        }
    }
    // Recorded, not silent. The emitted script says `not!0` where the source
    // said `not`, and anyone reading the two side by side has to be told why.
    diagnostics.warn(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                     "symbol '" + hir_name + "' is a reserved SMT-LIB name and is emitted "
                     "as '" + candidate + "'. The symbol is uninterpreted, so this is a "
                     "renaming and not a change of meaning");
    taken_names_.insert(candidate);
    return emit_names_.emplace(hir_name, candidate).first->second;
}

namespace {

// Generated names have reserved-name!N or __somt_hir_param_N spelling.
// Other source names cannot collide. Retain a conservative superset of those
// two forms, including quoted spellings checked by containsSmtSymbol.
void collectCollisionName(const std::string& name,
                          std::unordered_set<std::string>& out) {
    constexpr char parameter_prefix[] = "__somt_hir_param_";
    const std::size_t begin = !name.empty() && name.front() == '|' ? 1 : 0;
    if (name.find('!') != std::string::npos
        || name.compare(begin, sizeof(parameter_prefix) - 1, parameter_prefix) == 0) {
        out.insert(name);
    }
}

/** Include bound names, so generated names cannot capture free occurrences. */
void collectNames(const H::ExprPtr& root, std::unordered_set<std::string>& out,
                  std::unordered_set<const H::Expr*>& shared) {
    std::vector<const H::ExprPtr*> pending{&root};
    while (!pending.empty()) {
        const auto& expr = *pending.back();
        pending.pop_back();
        if (!expr) { continue; }
        if (expr.use_count() > 1 && !shared.insert(expr.get()).second) { continue; }
        if (!expr->name.empty()) { collectCollisionName(expr->name, out); }
        for (const auto& binder : expr->binders) { collectCollisionName(binder.name, out); }
        for (const auto& arg : expr->args) { pending.push_back(&arg); }
    }
}

} // namespace

bool HirToParser::lower(const H::ConstraintModel& model,
                        Uir::TranslationReport& report,
                        Uir::Diagnostics& diagnostics) {
    return lowerImpl(model, nullptr, false, report, diagnostics);
}

bool HirToParser::lowerPackedLinearPreamble(
    const H::ConstraintModel& model, Uir::TranslationReport& report,
    Uir::Diagnostics& diagnostics, bool stream_literal_bounds,
    bool stream_unused_declarations) {
    if (!model.packed_linear_rows) {
        diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                          "packed linear preamble requires packed numeric rows");
        return false;
    }
    return lowerImpl(model, nullptr, false, report, diagnostics, true,
                     stream_literal_bounds, stream_unused_declarations);
}

bool HirToParser::lowerConsuming(H::ConstraintModel& model,
                                 Uir::TranslationReport& report,
                                 Uir::Diagnostics& diagnostics) {
    return lowerImpl(model, &model, false, report, diagnostics);
}

bool HirToParser::lowerConsumingForTranslation(
    H::ConstraintModel& model, Uir::TranslationReport& report,
    Uir::Diagnostics& diagnostics) {
    return lowerImpl(model, &model, true, report, diagnostics);
}

bool HirToParser::lowerImpl(const H::ConstraintModel& model,
                            H::ConstraintModel* consumed,
                            bool release_metadata,
                            Uir::TranslationReport& report,
                            Uir::Diagnostics& diagnostics,
                            bool packed_linear_preamble,
                            bool stream_literal_bounds,
                            bool stream_unused_declarations) {
    const std::size_t objective_count = H::objectiveCountWithSoft(model);
    condAssert(parser_ != nullptr, "HirToParser: null parser");
    if (!model.scalar_var_ranges.empty() || model.packed_function_calls) {
        diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
            "compact scalar HIR requires the packed SMT-LIB streaming backend");
        return false;
    }
    if (!model.bool_var_ranges.empty() || !model.packed_bool_clauses.empty()) {
        diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
            "packed Boolean clause HIR requires the packed SMT-LIB streaming backend; "
            "ordinary parser lowering does not preserve packed ranges");
        return false;
    }
    if (model.packed_linear_rows != nullptr && !packed_linear_preamble) {
        diagnostics.error(Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT,
            "packed linear-row HIR requires the packed SMT-LIB streaming backend");
        return false;
    }
    // Capture expression-dependent statistics before consuming any roots.
    const auto quantifier_alternations = model.maxQuantifierAlternations();

    // Collect every possible generated-name collision BEFORE declarations,
    // so emitName's replacement for a reserved symbol can be checked against
    // the whole model rather than against the part declared so far. See
    // emitName in the header for what this is for.
    for (const auto& d : model.decls) { collectCollisionName(d.name, taken_names_); }
    for (const auto& f : model.funs) { collectCollisionName(f.name, taken_names_); }
    for (const auto& dt : model.datatypes) {
        collectCollisionName(dt.name, taken_names_);
        for (const auto& c : dt.constructors) {
            collectCollisionName(c.name, taken_names_);
            for (const auto& s : c.selectors) { collectCollisionName(s.name, taken_names_); }
        }
    }
    // Release raw-node cache before consuming any model expressions.
    {
        std::unordered_set<const H::Expr*> shared_names;
        for (const auto& f : model.funs) {
            collectNames(f.body, taken_names_, shared_names);
            for (const auto& binder : f.binders) { collectCollisionName(binder.name, taken_names_); }
        }
        for (const auto& c : model.constraints) { collectNames(c.formula, taken_names_, shared_names); }
        for (const auto& o : model.objectives) {
            collectCollisionName(o.name, taken_names_);
            collectNames(o.term, taken_names_, shared_names);
        }
    }

    // Explicit free constructors are registered before datatype declarations
    // and all term sorts. Their vector retains source order; all are declared
    // before datatype groups so forward sort references remain resolvable.
    for (const auto& sort : model.uninterpreted_sorts) {
        if (sort.name.empty()) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "an uninterpreted sort declaration has no name",
                              sort.loc);
            return false;
        }
        auto constructor = parser_->getSortManager()->createSortDec(
            sort.name, sort.arity);
        if (!constructor) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "could not declare sort '" + sort.name + "'",
                              sort.loc);
            return false;
        }
        parser_->getSymbolManager()->registerSort(sort.name, constructor);
    }
    if (release_metadata && consumed) {
        std::vector<H::UninterpretedSortDecl>().swap(consumed->uninterpreted_sorts);
    }

    // Datatypes before everything: a function's parameter, a variable, or a
    // selector's field sort may name one, and a sort cannot be resolved before
    // it is registered.
    //
    // Two passes, because a selector's sort may be the datatype being declared
    // (that is what makes a list a list) or one declared later in the group.
    // The first pass registers a placeholder sort under each name so the second
    // can resolve every reference; the engine's createDatatypeSort then fills in
    // the constructors.
    for (const auto& dt : model.datatypes) {
        // The placeholder carries the ARITY, so a selector's `(L X)` inside the
        // second pass instantiates rather than resolving to a bare name.
        parser_->getSymbolManager()->registerSort(
            dt.name, parser_->getSortManager()->createSortDec(
                dt.name, dt.params.size()));
    }
    for (const auto& dt : model.datatypes) {
        // Bound for exactly this datatype's constructors, as `par` binds them.
        dt_params_in_scope_.clear();
        dt_params_in_scope_.insert(dt.params.begin(), dt.params.end());
        std::vector<Sort::DtConstructor> ctors;
        ctors.reserve(dt.constructors.size());
        for (const auto& c : dt.constructors) {
            Sort::DtConstructor out;
            out.name = c.name;
            for (const auto& sel : c.selectors) {
                auto s = lowerSort(sel.sort, diagnostics);
                if (!s) { return false; }
                out.selectors.push_back(Sort::DtSelector{sel.name, std::move(s)});
            }
            ctors.push_back(std::move(out));
        }
        auto sort = parser_->getSortManager()->createDatatypeSort(dt.name, ctors);
        if (sort) { sort->coinductive = dt.coinductive; }
        if (sort && !dt.params.empty()) {
            // A parametric datatype is a sort CONSTRUCTOR: its arity and its
            // parameter names both have to reach the parser, or dumpSMT2 writes
            // an arity-0 declaration with no `par` and the script it emits is
            // not the one it read.
            sort->arity = dt.params.size();
            parser_->setDatatypeParams(dt.name, dt.params);
        }
        if (!sort) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "could not declare datatype '" + dt.name + "'", dt.loc);
            return false;
        }
        parser_->getSymbolManager()->registerSort(dt.name, sort);
        dt_params_in_scope_.clear();
    }
    if (release_metadata && consumed) {
        std::vector<H::DatatypeDecl>().swap(consumed->datatypes);
    }

    // Register uninterpreted functions first: applications may appear in the
    // first definition or constraint. Defined functions are installed after
    // globals exist and in dependency order below.
    for (const auto& f : model.funs) {
        if (f.body) { continue; }
        std::vector<std::shared_ptr<Sort>> params;
        params.reserve(f.params.size());
        for (const auto& ps : f.params) {
            auto s = lowerSort(ps, diagnostics);
            if (!s) { return false; }
            params.push_back(std::move(s));
        }
        auto result = lowerSort(f.result, diagnostics);
        if (!result) { return false; }
        if (!parser_->mkFuncDec(emitName(f.name, diagnostics), params, result)) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "could not declare function '" + f.name + "'", f.loc);
            return false;
        }
    }

    // Packed rows and literal bounds need names, not one Parser variable DAG
    // and hash-table entry per column. Materialize only numeric declarations
    // referenced by ordinary HIR; every other sort keeps its established path.
    // This is a conservative occurrence set: a shadowed IDENT can retain an
    // extra declaration, but cannot cause a free occurrence to be dropped.
    std::unordered_set<std::string_view> preamble_columns;
    if (stream_unused_declarations) {
        std::vector<const H::ExprPtr*> pending;
        for (const auto& function : model.funs) { pending.push_back(&function.body); }
        for (const auto& constraint : model.constraints) { pending.push_back(&constraint.formula); }
        for (const auto& objective : model.objectives) { pending.push_back(&objective.term); }
        for (const auto& declaration : model.decls) {
            const auto keep_bound = [&](const H::ExprPtr& bound) {
                if (bound && !(stream_literal_bounds
                               && H::isPackedLinearBoundLiteral(declaration, bound))) {
                    preamble_columns.insert(declaration.name);
                    pending.push_back(&bound);
                }
            };
            keep_bound(declaration.lower_bound);
            keep_bound(declaration.upper_bound);
        }
        std::unordered_set<const H::Expr*> shared;
        while (!pending.empty()) {
            const H::ExprPtr& expression = *pending.back();
            pending.pop_back();
            if (!expression) { continue; }
            if (expression.use_count() > 1 && !shared.insert(expression.get()).second) { continue; }
            if (expression->kind == H::ExprKind::IDENT) {
                preamble_columns.insert(expression->name);
            }
            for (const auto& argument : expression->args) { pending.push_back(&argument); }
        }
    }
    for (const auto& d : model.decls) {
        // Even a streamed declaration participates in the original order of
        // alpha-renaming, before definitions can introduce bound names.
        const std::string& emitted_name = emitName(d.name, diagnostics);
        if (stream_unused_declarations
            && (d.sort.kind == H::SortKind::INT || d.sort.kind == H::SortKind::REAL)
            && preamble_columns.find(d.name) == preamble_columns.end()) {
            continue;
        }
        std::shared_ptr<DAGNode> v;
        switch (d.sort.kind) {
        case H::SortKind::BOOL: v = parser_->mkVarBool(emitted_name); break;
        case H::SortKind::INT:  v = parser_->mkVarInt(emitted_name);  break;
        case H::SortKind::REAL: v = parser_->mkVarReal(emitted_name); break;
        default: {
            // Everything else -- arrays, bit-vectors, floats, strings and
            // uninterpreted sorts -- goes through the general mkVar with a
            // constructed sort. The three shorthands above exist only because
            // they predate it.
            auto sort = lowerSort(d.sort, diagnostics);
            if (sort) { v = parser_->mkVar(sort, emitted_name); }
            break;
        }
        }
        if (!v) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "could not declare variable '" + d.name + "'", d.loc);
            return false;
        }
        vars_[d.name] = v;
    }
    decltype(preamble_columns){}.swap(preamble_columns);

    // Acyclic helpers must follow their called definitions; explicitly
    // recursive SCCs are ordered as one unit. HIR type checking has already
    // validated which cycles carry an opt-in group label. Uninterpreted
    // functions were declared above.
    std::unordered_map<std::string, const H::FunDecl*> definitions;
    std::unordered_map<std::string, std::vector<const H::FunDecl*>> units;
    std::unordered_map<std::string, std::string> unit_for_function;
    for (const auto& f : model.funs) {
        if (!f.body) continue;
        definitions.emplace(f.name, &f);
        const std::string unit = f.recursive_group.empty()
            ? "F:" + f.name : "G:" + f.recursive_group;
        unit_for_function.emplace(f.name, unit);
        units[unit].push_back(&f);
    }
    std::unordered_map<std::string, unsigned char> unit_state;
    std::vector<std::string> unit_order;
    std::vector<const H::FunDecl*> definition_order;
    bool definition_order_ok = true;
    std::unordered_map<std::string, std::vector<std::string>> unit_dependencies;
    for (const auto& entry : units) {
        auto& dependencies = unit_dependencies[entry.first];
        std::unordered_set<std::string> dependency_seen;
        for (const H::FunDecl* function : entry.second) {
            std::unordered_set<const H::Expr*> seen;
            std::vector<const H::Expr*> pending{function->body.get()};
            while (!pending.empty()) {
                const auto* expression = pending.back();
                pending.pop_back();
                if (!expression || !seen.insert(expression).second) { continue; }
                if (expression->kind == H::ExprKind::APPLY
                    && definitions.count(expression->name)) {
                    const auto& dependency = unit_for_function.at(expression->name);
                    if (dependency != entry.first && dependency_seen.insert(dependency).second) {
                        dependencies.push_back(dependency);
                    }
                }
                for (auto it = expression->args.rbegin(); it != expression->args.rend(); ++it) {
                    pending.push_back(it->get());
                }
            }
        }
    }
    struct UnitFrame { std::string unit; std::size_t next_dependency = 0; };
    for (const auto& f : model.funs) {
        if (!f.body) { continue; }
        const auto& start = unit_for_function.at(f.name);
        if (unit_state.count(start)) { continue; }
        std::vector<UnitFrame> pending{{start}};
        unit_state.emplace(start, 1);
        while (!pending.empty()) {
            auto& frame = pending.back();
            const auto& dependencies = unit_dependencies.at(frame.unit);
            if (frame.next_dependency < dependencies.size()) {
                const std::string dependency = dependencies[frame.next_dependency++];
                const auto known = unit_state.find(dependency);
                if (known != unit_state.end()) {
                    if (known->second == 1) {
                        const H::FunDecl* function = units.at(dependency).front();
                        diagnostics.error(ErrorCode::E_INTERNAL,
                            "recursive or cyclic HIR function definition involving '"
                                + function->name + "'", function->loc);
                        definition_order_ok = false;
                    }
                } else {
                    unit_state.emplace(dependency, 1);
                    pending.push_back({dependency});
                }
                continue;
            }
            unit_state[frame.unit] = 2;
            unit_order.push_back(frame.unit);
            pending.pop_back();
        }
    }
    if (!definition_order_ok) { return false; }
    for (const std::string& unit : unit_order) {
        const auto& members = units.at(unit);
        definition_order.insert(definition_order.end(), members.begin(), members.end());
    }

    // Estimate inline expansion in dependency order, stopping at definitions
    // already retained as calls. A chain of small helpers can expand much more
    // than a single large body, so local operator counts alone are insufficient.
    constexpr std::size_t inline_operation_limit = 512;
    // Permit at most twice the ordinary macro budget for finite array-read
    // leaves. Calls still contribute their full expanded cost to callers;
    // a hierarchy cannot repeatedly acquire this larger leaf-only allowance.
    constexpr std::size_t array_leaf_operation_limit = 2 * inline_operation_limit;
    std::unordered_map<std::string, std::size_t> inline_operations;

    // Lower each body under fresh function-parameter nodes. These are scoped
    // only while its body is built; the emitted define-fun owns their binding.
    for (const H::FunDecl* function : definition_order) {
        std::vector<std::shared_ptr<DAGNode>> params;
        std::vector<std::string> pushed;
        std::vector<std::pair<std::string, std::shared_ptr<DAGNode>>> shadowed;
        params.reserve(function->binders.size());
        const auto restore_bound_scope = [&]() {
            for (auto it = pushed.rbegin(); it != pushed.rend(); ++it) {
                const auto previous = std::find_if(
                    shadowed.begin(), shadowed.end(),
                    [&](const auto& entry) { return entry.first == *it; });
                if (previous == shadowed.end()) { bound_.erase(*it); }
                else { bound_[*it] = previous->second; }
            }
        };
        for (const H::Binder& binder : function->binders) {
            auto sort = lowerSort(binder.sort, diagnostics);
            if (!sort) { restore_bound_scope(); return false; }
            // HIR distinguishes a BOUND_VAR from a free IDENT with the same
            // spelling. The emitted SMT body is textually scoped, so using the
            // source spelling for both would capture the global occurrence
            // (for example (+ bound-x global-x) becomes (+ x x)). Give every
            // function parameter a fresh emitted name without changing the
            // global emit_names_ mapping used by IDENT lowering.
            std::string emitted_parameter;
            for (;;) {
                emitted_parameter = "__somt_hir_param_"
                    + std::to_string(next_function_parameter_suffix_++);
                if (!containsSmtSymbol(taken_names_, emitted_parameter)
                    && !SOMTParser::isBuiltinNameReservedAgainstUserFun(emitted_parameter)) {
                    taken_names_.insert(emitted_parameter);
                    break;
                }
            }
            auto parameter = parser_->mkFunParamVar(sort, emitted_parameter);
            if (!parameter) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "could not create parameter '" + binder.name
                                      + "' for function '" + function->name + "'",
                                  function->loc);
                restore_bound_scope();
                return false;
            }
            const auto previous = bound_.find(binder.name);
            if (previous != bound_.end()) {
                shadowed.emplace_back(binder.name, previous->second);
            }
            bound_[binder.name] = parameter;
            pushed.push_back(binder.name);
            params.push_back(std::move(parameter));
        }
        auto body = lowerExpr(function->body, diagnostics);
        restore_bound_scope();
        if (!body) { return false; }
        auto result = lowerSort(function->result, diagnostics);
        if (!result) { return false; }
        // Ordinary define-fun is a macro in common SMT parsers. Retain an
        // acyclic definition once its transitive expansion becomes large,
        // including source-visible definitions. define-fun-rec then represents
        // the same unique equation without requiring eager macro expansion.
        // A bounded finite array-read leaf stays an ordinary macro so callers
        // of the emitted script can see its individual array observations.
        // Explicit recursive groups keep their existing equation semantics.
        const bool array_leaf = finiteArrayReadLeaf(*function, array_leaf_operation_limit);
        const std::size_t operation_limit = array_leaf
            ? array_leaf_operation_limit : inline_operation_limit;
        std::unordered_set<const H::Expr*> retained_nodes;
        std::vector<const H::Expr*> pending{function->body.get()};
        std::size_t operators = 0;
        while (!pending.empty() && operators < operation_limit) {
            const H::Expr* expression = pending.back(); pending.pop_back();
            if (!retained_nodes.insert(expression).second) { continue; }
            std::size_t contribution = expression->kind == H::ExprKind::OP ? 1 : 0;
            if (expression->kind == H::ExprKind::APPLY) {
                const auto dependency = inline_operations.find(expression->name);
                contribution = dependency == inline_operations.end()
                    ? 1 : dependency->second;
            }
            operators += std::min(operation_limit - operators, contribution);
            for (const auto& child : expression->args) { pending.push_back(child.get()); }
        }
        const bool retained = !params.empty() && operators >= operation_limit;
        const bool recursive = retained || !function->recursive_group.empty();
        inline_operations.emplace(function->name, recursive ? 1 : operators);
        auto defined = recursive
            ? parser_->mkFuncRec(emitName(function->name, diagnostics), params, result, body)
            : parser_->mkFuncDef(emitName(function->name, diagnostics), params, result, body);
        if (!defined) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "could not define function '" + function->name + "'",
                              function->loc);
            return false;
        }
        if (retained && function->recursive_group.empty()) {
            report.addChoice({function->name, "defined-function",
                "retained-acyclic-definition", Uir::Fidelity::exact(),
                "An acyclic definition whose estimated transitive macro expansion "
                "reaches 512 operations is emitted with define-fun-rec; retained "
                "callees remain shared, and dependency validation proves the same "
                "unique function equation"});
        } else if (array_leaf && operators >= inline_operation_limit) {
            report.addChoice({function->name, "defined-function",
                "finite-array-read-macro", Uir::Fidelity::exact(),
                "An acyclic leaf with fewer than 1024 operations and only "
                "literal-index reads of its array parameters is emitted with "
                "define-fun to expose its cells; callers account for the full "
                "macro expansion, while larger or non-leaf definitions retain "
                "the existing sharing policy"});
        }
        if (consumed) {
            consumed->funs[function - model.funs.data()].body.reset();
        }
    }
    // Register each explicit HIR SCC only after all of its bodies have become
    // recursive parser nodes. The checked builder refuses incomplete or
    // unrelated groups and records the scope used by define-funs-rec dumping.
    std::unordered_set<std::string> registered_groups;
    for (const H::FunDecl& function : model.funs) {
        if (function.recursive_group.empty()
            || !registered_groups.insert(function.recursive_group).second) {
            continue;
        }
        std::vector<std::string> names;
        for (const H::FunDecl& member : model.funs) {
            if (member.recursive_group == function.recursive_group) {
                names.push_back(emitName(member.name, diagnostics));
            }
        }
        if (!parser_->mkFuncRecGroup(names)) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "could not register recursive function group '"
                                  + function.recursive_group + "'",
                              function.loc);
            return false;
        }
    }
    // Function names were registered with the upfront declarations. Reorder
    // just this model's entries so declarations come first, followed by the
    // dependency-ordered definition units. This keeps external references
    // before their users and keeps each recursive SCC contiguous at its first
    // member; the symbol table itself is unchanged.
    for (const H::FunDecl& function : model.funs) {
        parser_->getSymbolManager()->removeFunctionName(emitName(function.name, diagnostics));
    }
    for (const H::FunDecl& function : model.funs) {
        if (definitions.find(function.name) == definitions.end()) {
            parser_->getSymbolManager()->addFunctionName(emitName(function.name, diagnostics));
        }
    }
    for (const H::FunDecl* function : definition_order) {
        parser_->getSymbolManager()->addFunctionName(emitName(function->name, diagnostics));
    }
    if (release_metadata && consumed) {
        std::vector<H::FunDecl>().swap(consumed->funs);
    }

    // Bounds are ordinary assertions; nothing about them is solver-specific.
    for (const auto& d : model.decls) {
        if (d.lower_bound && !(stream_literal_bounds
                              && H::isPackedLinearBoundLiteral(d, d.lower_bound))) {
            auto lb = lowerExpr(d.lower_bound, diagnostics);
            if (!lb) { return false; }
            parser_->assert(parser_->mkGe(vars_[d.name], lb));
        }
        if (d.upper_bound && !(stream_literal_bounds
                              && H::isPackedLinearBoundLiteral(d, d.upper_bound))) {
            auto ub = lowerExpr(d.upper_bound, diagnostics);
            if (!ub) { return false; }
            parser_->assert(parser_->mkLe(vars_[d.name], ub));
        }
    }
    if (release_metadata && consumed) {
        std::vector<H::VarDecl>().swap(consumed->decls);
    }

    const std::size_t lowered_constraint_count = model.constraints.size();
    for (std::size_t constraint_index = 0;
         constraint_index < model.constraints.size(); ++constraint_index) {
        const auto& c = model.constraints[constraint_index];
        // That c.formula is Bool is a precondition, established by
        // Uir::Hir::typeCheck before any pass runs (see hir/typecheck.h).
        // Parser::assert accepts any node, so an Int formula reaching here
        // becomes a literal `(assert x)` that no solver will read -- which is
        // exactly what happened before that check existed.
        // Release each immutable HIR child after lowering it. Accumulate the
        // native children so successful lowering preserves the original AND
        // structure and serialized target. Soft constraints keep their one
        // weighted formula. If a child fails, assert the completed prefix and
        // retain the unlowered suffix under the partial-consumption contract.
        const bool split_hard_and = consumed && !c.soft && c.formula
            && c.formula->kind == H::ExprKind::OP
            && c.formula->op == H::Op::AND && c.formula->args.size() > 1;
        if (split_hard_and) {
            // Splitting an AND only releases its HIR children incrementally;
            // they remain one lowering root. Keep its memoized shared terms
            // across conjuncts, as lowerExpr would for the unsplit formula.
            // Quantifiers still create their own scope epochs. No new HIR
            // expressions are allocated until a failed suffix is rebuilt,
            // and this guard discards all raw-pointer keys on either exit.
            Detail::clearExpressionRootCache(expr_cache_);
            lower_scope_epoch_ = ++next_lower_scope_epoch_;
            struct ConjunctRootScope {
                decltype(expr_cache_)& cache;
                std::size_t& depth;
                ConjunctRootScope(decltype(expr_cache_)& c, std::size_t& d)
                    : cache(c), depth(d) { ++depth; }
                // Keep destruction allocation-free. The next root entry
                // releases oversized capacity even when this clear left it empty.
                ~ConjunctRootScope() { --depth; cache.clear(); }
            } root_scope(expr_cache_, lower_expr_depth_);
            const Uir::SourceLoc formula_loc = c.formula->loc;
            std::vector<H::ExprPtr> pending = c.formula->args;
            std::vector<std::shared_ptr<DAGNode>> conjuncts;
            conjuncts.reserve(pending.size());
            consumed->constraints[constraint_index].formula.reset();
            for (std::size_t child = 0; child < pending.size(); ++child) {
                auto node = lowerExpr(pending[child], diagnostics);
                if (!node) {
                    for (const auto& completed : conjuncts) {
                        parser_->assert(completed);
                    }
                    std::vector<H::ExprPtr> remainder;
                    remainder.reserve(pending.size() - child);
                    for (std::size_t i = child; i < pending.size(); ++i) {
                        remainder.push_back(std::move(pending[i]));
                    }
                    consumed->constraints[constraint_index].formula =
                        remainder.size() == 1
                            ? std::move(remainder.front())
                            : H::mkOp(H::Op::AND, std::move(remainder), formula_loc);
                    return false;
                }
                conjuncts.push_back(std::move(node));
                pending[child].reset();
            }
            parser_->assert(parser_->mkAnd(conjuncts));
            if (release_metadata) {
                consumed->constraints[constraint_index] = H::Constraint{};
            }
            continue;
        }

        auto n = lowerExpr(c.formula, diagnostics);
        if (!n) {
            return false;
        }
        // parser_->assert() would turn a soft constraint into a hard one --
        // changing the problem from "violate this at cost w" to "never violate
        // this", which can turn a satisfiable MaxSMT instance UNSAT. Until the
        // engine had a public builder for a soft assertion this was refused
        // rather than hardened, because a wrong answer reported as success is
        // worse than a recorded failure.
        if (c.soft) {
            // Lowered rather than refused, since 2026-08-12. The engine models
            // soft assertions and had no public builder for one, so this used
            // to report E_UNSUPPORTED_CONSTRUCT for a construct the target
            // could express -- and turning a soft constraint into a hard one
            // instead would have changed the problem, which is why refusing was
            // right until the builder existed.
            //
            // The weight is a double in the HIR and SMT-LIB takes a numeral, so
            // an integral weight is emitted as an integer and a fractional one
            // as a decimal. MaxSAT weights are integers (wcnf.md §2); the
            // double is what the HIR happens to carry.
            std::shared_ptr<DAGNode> w;
            if (!c.weight_text.empty()) {
                // Exact, and of unbounded magnitude: a WBO cost may exceed any
                // machine integer and must not go through the double.
                w = parser_->mkConstInt(c.weight_text);
            } else {
                const double iw = std::floor(c.weight);
                if (iw == c.weight && std::abs(c.weight) < 9.0e15) {
                    w = parser_->mkConstInt(static_cast<long long>(iw));
                } else {
                    std::ostringstream ss;
                    ss << std::setprecision(17) << c.weight;
                    w = parser_->mkConstReal(ss.str());
                }
            }
            parser_->assertSoft(n, w, c.group);
        } else {
            parser_->assert(n);
        }
        if (consumed) {
            consumed->constraints[&c - model.constraints.data()].formula.reset();
            if (release_metadata) {
                consumed->constraints[constraint_index] = H::Constraint{};
            }
        }
    }
    if (release_metadata && consumed) {
        std::vector<H::Constraint>().swap(consumed->constraints);
    }

    // vars_, not model.decls: the map is keyed by name, so it holds what was
    // actually declared. decls.size() counted a repeated `var int: x` twice
    // while emitting one declare-fun, and num_vars is a column in the
    // experiment's own results table -- a size figure that does not match the
    // emitted script is worse than a missing one. Uir::Hir::typeCheck now
    // rejects a duplicate declaration outright, so the two agree on every input
    // that reaches here through translate(); they can still diverge for a
    // caller that lowers a model directly, and this is the honest number then.
    // The size of the emitted DAG, counted over DISTINCT nodes rather than by
    // walking each assertion as a tree. Nodes are hash-consed, so a shared
    // subterm is one node reachable by many paths; a tree walk would report a
    // number that can be exponentially larger than what was emitted, and on
    // anything Tseitin touched it would not terminate in reasonable time.
    //
    // This was declared, serialised into the report JSON and bound to Python,
    // and never assigned: every translation in the tree reported 0 smt nodes,
    // including the 432 rows of the corpus sweep whose whole point is size.
    if (report.detailsEnabled()) {
        std::unordered_set<const DAGNode*> seen;
        std::vector<std::shared_ptr<DAGNode>> stack;
        for (const std::shared_ptr<DAGNode>& a : parser_->getAssertions()) {
            if (a) { stack.push_back(a); }
        }
        for (const std::shared_ptr<DAGNode>& a : parser_->getSoftAssertions()) {
            if (a) { stack.push_back(a); }
        }
        while (!stack.empty()) {
            const std::shared_ptr<DAGNode> cur = stack.back();
            stack.pop_back();
            if (!cur || !seen.insert(cur.get()).second) { continue; }
            for (const std::shared_ptr<DAGNode>& kid : cur->getChildren()) {
                if (kid) { stack.push_back(kid); }
            }
        }
        report.mutableStats().num_smt_nodes = seen.size();
    }

    report.mutableStats().num_vars = stream_unused_declarations ? model.decls.size() : vars_.size();
    report.mutableStats().num_constraints = lowered_constraint_count;
    report.mutableStats().num_objectives = objective_count;
    report.mutableStats().max_quantifier_alternations = quantifier_alternations;
    return true;
}


void HirToParser::retainObjectiveBindings(const H::ConstraintModel& model) {
    std::unordered_set<std::string> needed;
    std::unordered_set<const H::Expr*> seen;
    // Cursor frames avoid a stack proportional to an n-ary objective's width.
    std::vector<std::pair<const H::Expr*, std::size_t>> stack;
    const auto visit = [&](const H::Expr* expr) {
        if (!expr || !seen.insert(expr).second) { return; }
        if (expr->kind == H::ExprKind::IDENT) { needed.insert(expr->name); }
        stack.emplace_back(expr, 0);
    };
    for (const auto& objective : model.objectives) {
        visit(objective.term.get());
        while (!stack.empty()) {
            auto& frame = stack.back();
            if (frame.second == frame.first->args.size()) {
                stack.pop_back();
            } else {
                const H::Expr* child = frame.first->args[frame.second++].get();
                visit(child);
            }
        }
    }
    for (auto it = vars_.begin(); it != vars_.end();) {
        if (needed.count(it->first) == 0) { it = vars_.erase(it); }
        else { ++it; }
    }
    if (vars_.bucket_count() > 2 * vars_.size()) { vars_.rehash(0); }
}

} // namespace SOMTParser::Lower
