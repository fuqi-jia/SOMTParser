/* -*- Source -*-
 * ParserToHir — see the header for why this exists and what it refuses.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/lowering/parser_to_hir.h"

#include "somtparser/core/kind.h"

#include <algorithm>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lower {

namespace H = Uir::Hir;
using Uir::ErrorCode;

namespace {

std::string boundSymbolKey(const std::string& name) {
    return name.size() >= 2 && name.front() == '|' && name.back() == '|'
        ? name.substr(1, name.size() - 2) : name;
}

bool symbolicFpConstructor(const std::shared_ptr<DAGNode>& node) {
    if (!node || !node->isCFP() || node->getName() != "(fp_bit_representation)"
        || node->getChildrenSize() != 3) { return false; }
    for (std::size_t i = 0; i < 3; ++i) {
        if (!node->getChild(i)->isCBV()) { return true; }
    }
    return false;
}

/** Build an application, expanding the SMT-LIB argument-list attributes the
 *  HIR's operators do not carry.
 *
 * Three of them, and none is a leniency -- each is what the standard says the
 * term MEANS, so refusing a three-argument `=` refuses a legal script:
 *
 *   :chainable    `(= a b c)`  is `(and (= a b) (= b c))`, and likewise for
 *                 `<`, `<=`, `>`, `>=`. ADJACENT pairs, not all pairs: that is
 *                 the standard's definition, and for the orderings it is the
 *                 only one that is even equivalent -- `(< a b c)` says a<b<c
 *                 and says nothing directly about a and c beyond what follows.
 *   :right-assoc  `(=> a b c)` is `(=> a (=> b c))`. Left-nesting would be a
 *                 different formula, not a different spelling.
 *   n-ary         everything else here already is, and passes straight through.
 *
 * The expansion costs SIZE: `(= a b c)` mentions b twice, and a chain of k
 * arguments becomes k-1 comparisons. That is exact and it is the same trade
 * `let` makes, so it is recorded here rather than discovered in a script that
 * is bigger than its source.
 */
bool isChainable(H::Op op) {
    switch (op) {
    case H::Op::EQ: case H::Op::LE: case H::Op::LT:
    case H::Op::GE: case H::Op::GT:
        return true;
    default:
        return false;
    }
}

} // namespace

ParserToHir::ParserToHir(ParserPtr parser) : parser_(std::move(parser)) {
    if (!parser_) { return; }
    for (const auto& variable : parser_->getDeclaredVariables()) {
        reserved_names_.insert(boundSymbolKey(variable->getName()));
    }
    for (const auto& function : parser_->getFunctions()) {
        reserved_names_.insert(boundSymbolKey(function->getName()));
    }
}

std::string ParserToHir::freshBoundName(const std::string& source, bool parameter) {
    const std::string key = boundSymbolKey(source);
    std::string candidate;
    do {
        const auto suffix = std::to_string(++rename_seq_);
        candidate = parameter ? "p!" + suffix + "!" + key : key + "!" + suffix;
    } while (reserved_names_.count(candidate) || active_bound_names_.count(candidate));
    reserved_names_.insert(candidate);
    // Keep quoted spellings quoted: a space in a source symbol is still a
    // space after alpha-renaming, not part of a legal simple symbol.
    return source.size() >= 2 && source.front() == '|' && source.back() == '|'
        ? "|" + candidate + "|" : candidate;
}

H::ExprPtr ParserToHir::mkNary(H::Op op, std::vector<H::ExprPtr> args,
                               Uir::Diagnostics& diagnostics) {
    if (args.size() <= 2) { return H::mkOp(op, std::move(args)); }
    if (isChainable(op)) {
        std::vector<H::ExprPtr> conj;
        conj.reserve(args.size() - 1);
        for (std::size_t i = 0; i + 1 < args.size(); ++i) {
            conj.push_back(H::mkOp(op, {args[i], args[i + 1]}));
        }
        return H::mkOp(H::Op::AND, std::move(conj));
    }
    if (op == H::Op::IMPLIES) {
        // Right-nested, so the fold runs from the END: `(=> a b c)` is
        // `(=> a (=> b c))`, and building it left-first would give
        // `(=> (=> a b) c)` -- a formula with a different truth table.
        H::ExprPtr acc = args.back();
        for (std::size_t i = args.size() - 1; i-- > 0;) {
            acc = H::mkOp(H::Op::IMPLIES, {args[i], acc});
        }
        return acc;
    }
    // Genuinely n-ary in both layers.
    (void)diagnostics;
    return H::mkOp(op, std::move(args));
}

namespace {

/** NODE_KIND -> Hir::Op, for the operators both layers have.
 *
 * The inverse of HirToParser's dispatch, and deliberately written out rather
 * than derived: the forward direction is a switch with structural special cases
 * (indexed operators, arity checks), so there is no table to invert. Anything
 * absent here is refused by name, which is why the table being incomplete is a
 * coverage statement rather than a bug.
 *
 * Integer division is the interesting entry. The engine has ONE `div` and it is
 * SMT-LIB's, which is Euclidean, so NT_DIV_INT lifts to DIV_EUCLID -- not to
 * DIV_TRUNC, and not to a plain DIV, which does not exist. A script that
 * reached this parser through HirToParser as a truncating division comes back
 * as the correction term it was lowered to, which is the honest answer: the
 * script really does say that.
 */
const std::unordered_map<NODE_KIND, H::Op>& opTable() {
    static const std::unordered_map<NODE_KIND, H::Op> t = {
        {NODE_KIND::NT_AND, H::Op::AND},
        {NODE_KIND::NT_OR, H::Op::OR},
        {NODE_KIND::NT_NOT, H::Op::NOT},
        {NODE_KIND::NT_XOR, H::Op::XOR},
        {NODE_KIND::NT_IMPLIES, H::Op::IMPLIES},
        {NODE_KIND::NT_DISTINCT, H::Op::DISTINCT},
        {NODE_KIND::NT_DISTINCT_BOOL, H::Op::DISTINCT},
        {NODE_KIND::NT_DISTINCT_OTHER, H::Op::DISTINCT},
        {NODE_KIND::NT_NEG, H::Op::NEG},
        {NODE_KIND::NT_ABS, H::Op::ABS},
        {NODE_KIND::NT_EQ, H::Op::EQ},
        {NODE_KIND::NT_EQ_BOOL, H::Op::EQ},
        {NODE_KIND::NT_EQ_OTHER, H::Op::EQ},
        {NODE_KIND::NT_LE, H::Op::LE},
        {NODE_KIND::NT_LT, H::Op::LT},
        {NODE_KIND::NT_GE, H::Op::GE},
        {NODE_KIND::NT_GT, H::Op::GT},
        {NODE_KIND::NT_ADD, H::Op::ADD},
        {NODE_KIND::NT_SUB, H::Op::SUB},
        {NODE_KIND::NT_MUL, H::Op::MUL},
        {NODE_KIND::NT_DIV_INT, H::Op::DIV_EUCLID},
        {NODE_KIND::NT_MOD, H::Op::MOD_EUCLID},
        {NODE_KIND::NT_DIV_REAL, H::Op::DIV_REAL},
        {NODE_KIND::NT_ITE, H::Op::ITE},
        {NODE_KIND::NT_SELECT, H::Op::SELECT},
        {NODE_KIND::NT_STORE, H::Op::STORE},
        {NODE_KIND::NT_ARRAY_MAP_AND, H::Op::ARRAY_MAP_AND},
        {NODE_KIND::NT_ARRAY_MAP_OR, H::Op::ARRAY_MAP_OR},
        {NODE_KIND::NT_ARRAY_MAP_NOT, H::Op::ARRAY_MAP_NOT},

        {NODE_KIND::NT_BV_NOT, H::Op::BV_NOT},
        {NODE_KIND::NT_BV_NEG, H::Op::BV_NEG},
        {NODE_KIND::NT_BV_AND, H::Op::BV_AND},
        {NODE_KIND::NT_BV_OR, H::Op::BV_OR},
        {NODE_KIND::NT_BV_XOR, H::Op::BV_XOR},
        {NODE_KIND::NT_BV_NAND, H::Op::BV_NAND},
        {NODE_KIND::NT_BV_NOR, H::Op::BV_NOR},
        {NODE_KIND::NT_BV_XNOR, H::Op::BV_XNOR},
        {NODE_KIND::NT_BV_ADD, H::Op::BV_ADD},
        {NODE_KIND::NT_BV_SUB, H::Op::BV_SUB},
        {NODE_KIND::NT_BV_MUL, H::Op::BV_MUL},
        {NODE_KIND::NT_BV_UDIV, H::Op::BV_UDIV},
        {NODE_KIND::NT_BV_UREM, H::Op::BV_UREM},
        {NODE_KIND::NT_BV_SDIV, H::Op::BV_SDIV},
        {NODE_KIND::NT_BV_SREM, H::Op::BV_SREM},
        {NODE_KIND::NT_BV_SMOD, H::Op::BV_SMOD},
        {NODE_KIND::NT_BV_SHL, H::Op::BV_SHL},
        {NODE_KIND::NT_BV_LSHR, H::Op::BV_LSHR},
        {NODE_KIND::NT_BV_ASHR, H::Op::BV_ASHR},
        {NODE_KIND::NT_BV_ULT, H::Op::BV_ULT},
        {NODE_KIND::NT_BV_ULE, H::Op::BV_ULE},
        {NODE_KIND::NT_BV_UGT, H::Op::BV_UGT},
        {NODE_KIND::NT_BV_UGE, H::Op::BV_UGE},
        {NODE_KIND::NT_BV_SLT, H::Op::BV_SLT},
        {NODE_KIND::NT_BV_SLE, H::Op::BV_SLE},
        {NODE_KIND::NT_BV_SGT, H::Op::BV_SGT},
        {NODE_KIND::NT_BV_SGE, H::Op::BV_SGE},
        {NODE_KIND::NT_BV_CONCAT, H::Op::BV_CONCAT},
        {NODE_KIND::NT_BV_COMP, H::Op::BV_COMP},

        // Spelled differently on the two sides, so the names do not line up and
        // each has to be written out.
        {NODE_KIND::NT_STR_IN_REG, H::Op::STR_IN_RE},
        {NODE_KIND::NT_STR_TO_REG, H::Op::STR_TO_RE},

        // ---- Conversions between the numeric sorts ----
        {NODE_KIND::NT_TO_INT, H::Op::TO_INT},
        {NODE_KIND::NT_TO_REAL, H::Op::TO_REAL},
        {NODE_KIND::NT_IS_INT, H::Op::IS_INT},
        {NODE_KIND::NT_BV_TO_NAT, H::Op::BV_TO_NAT},
        {NODE_KIND::NT_BV_TO_INT, H::Op::BV_TO_INT},
        // ---- Strings ----
        {NODE_KIND::NT_STR_LEN, H::Op::STR_LEN},
        {NODE_KIND::NT_STR_CONCAT, H::Op::STR_CONCAT},
        {NODE_KIND::NT_STR_SUBSTR, H::Op::STR_SUBSTR},
        {NODE_KIND::NT_STR_INDEXOF, H::Op::STR_INDEXOF},
        {NODE_KIND::NT_STR_REPLACE, H::Op::STR_REPLACE},
        {NODE_KIND::NT_STR_REPLACE_ALL, H::Op::STR_REPLACE_ALL},
        {NODE_KIND::NT_STR_LT, H::Op::STR_LT},
        {NODE_KIND::NT_STR_LE, H::Op::STR_LE},
        {NODE_KIND::NT_STR_CONTAINS, H::Op::STR_CONTAINS},
        {NODE_KIND::NT_STR_PREFIXOF, H::Op::STR_PREFIXOF},
        {NODE_KIND::NT_STR_SUFFIXOF, H::Op::STR_SUFFIXOF},
        {NODE_KIND::NT_STR_FROM_INT, H::Op::STR_FROM_INT},
        {NODE_KIND::NT_STR_TO_INT, H::Op::STR_TO_INT},
        {NODE_KIND::NT_STR_TO_CODE, H::Op::STR_TO_CODE},
        {NODE_KIND::NT_STR_IS_DIGIT, H::Op::STR_IS_DIGIT},
        {NODE_KIND::NT_STR_INDEXOF_REG, H::Op::STR_INDEXOF_RE},
        {NODE_KIND::NT_STR_REPLACE_REG, H::Op::STR_REPLACE_RE},
        {NODE_KIND::NT_STR_REPLACE_REG_ALL, H::Op::STR_REPLACE_RE_ALL},
        {NODE_KIND::NT_STR_FROM_CODE, H::Op::STR_FROM_CODE},
        // `ubv_to_int` and `sbv_to_int` are the engine's other spellings of
        // `bv2nat` and `bv2int` -- the same two operators, so the same two HIR
        // ops. Absent from the table while their aliases were present, which is
        // how an alias-shaped gap hides.
        {NODE_KIND::NT_UBV_TO_INT, H::Op::BV_TO_NAT},
        {NODE_KIND::NT_SBV_TO_INT, H::Op::BV_TO_INT},
        // ---- Regular expressions --------------------------------------
        //
        // The whole cluster was absent, and every operator it needs already
        // existed in the HIR: this was a table that had not been filled in, not
        // a missing feature. `test/instances/strings.smt2` -- a file in this
        // repository that the engine has always parsed -- failed with "'re.++'
        // has no HIR counterpart".
        //
        // The names differ on the two sides (the engine says REG, the HIR says
        // RE), which is exactly the kind of seam a table is for.
        {NODE_KIND::NT_STR_TO_REG, H::Op::STR_TO_RE},
        {NODE_KIND::NT_STR_IN_REG, H::Op::STR_IN_RE},
        {NODE_KIND::NT_REG_CONCAT, H::Op::RE_CONCAT},
        {NODE_KIND::NT_REG_UNION, H::Op::RE_UNION},
        {NODE_KIND::NT_REG_INTER, H::Op::RE_INTER},
        {NODE_KIND::NT_REG_DIFF, H::Op::RE_DIFF},
        {NODE_KIND::NT_REG_STAR, H::Op::RE_STAR},
        {NODE_KIND::NT_REG_PLUS, H::Op::RE_PLUS},
        {NODE_KIND::NT_REG_OPT, H::Op::RE_OPT},
        {NODE_KIND::NT_REG_COMPLEMENT, H::Op::RE_COMPLEMENT},
        {NODE_KIND::NT_REG_RANGE, H::Op::RE_RANGE},
        // `str.at` is the engine's NT_STR_CHARAT; same operator, other name.
        {NODE_KIND::NT_STR_CHARAT, H::Op::STR_AT},
        // ---- Sets ----
        {NODE_KIND::NT_SET_SINGLETON, H::Op::SET_SINGLETON},
        {NODE_KIND::NT_SET_UNION, H::Op::SET_UNION},
        {NODE_KIND::NT_SET_INTER, H::Op::SET_INTER},
        {NODE_KIND::NT_SET_MINUS, H::Op::SET_MINUS},
        {NODE_KIND::NT_SET_MEMBER, H::Op::SET_MEMBER},
        {NODE_KIND::NT_SET_SUBSET, H::Op::SET_SUBSET},
        {NODE_KIND::NT_SET_CARD, H::Op::SET_CARD},
        {NODE_KIND::NT_SET_INSERT, H::Op::SET_INSERT},
        {NODE_KIND::NT_SET_COMPLEMENT, H::Op::SET_COMPLEMENT},
        // ---- Tuples ----
        // Only the CONSTRUCTOR is a table entry. tuple.unit is a constant, and
        // the other three are indexed, so all four of those are handled
        // structurally in liftExpr -- the same split the bit-vector cluster
        // has, and for the same reason.
        {NODE_KIND::NT_TUPLE_CONSTRUCTOR, H::Op::TUPLE},
        // ---- Floating point. The rounding mode is the first child, so
        //      nothing special is needed here -- it lifts as an ordinary
        //      argument and mkOp reads the value sort from args[1].
        {NODE_KIND::NT_FP_ADD, H::Op::FP_ADD},
        {NODE_KIND::NT_FP_SUB, H::Op::FP_SUB},
        {NODE_KIND::NT_FP_MUL, H::Op::FP_MUL},
        {NODE_KIND::NT_FP_DIV, H::Op::FP_DIV},
        {NODE_KIND::NT_FP_ABS, H::Op::FP_ABS},
        {NODE_KIND::NT_FP_NEG, H::Op::FP_NEG},
        {NODE_KIND::NT_FP_REM, H::Op::FP_REM},
        {NODE_KIND::NT_FP_FMA, H::Op::FP_FMA},
        {NODE_KIND::NT_FP_SQRT, H::Op::FP_SQRT},
        {NODE_KIND::NT_FP_ROUND_TO_INTEGRAL, H::Op::FP_ROUND_TO_INTEGRAL},
        {NODE_KIND::NT_FP_MIN, H::Op::FP_MIN},
        {NODE_KIND::NT_FP_MAX, H::Op::FP_MAX},
        {NODE_KIND::NT_FP_LT, H::Op::FP_LT},
        {NODE_KIND::NT_FP_GT, H::Op::FP_GT},
        {NODE_KIND::NT_FP_EQ, H::Op::FP_EQ},
        // The comparison and classification operators the table lacked. Every
        // one already existed in the HIR -- `fp.leq` is FP_LEQ -- so this was
        // the same unfilled-table shape as the regex cluster, and
        // `test/instances/fp.smt2` is what named it.
        {NODE_KIND::NT_FP_LE, H::Op::FP_LEQ},
        {NODE_KIND::NT_FP_GE, H::Op::FP_GEQ},
        {NODE_KIND::NT_FP_IS_INF, H::Op::FP_IS_INFINITE},
        {NODE_KIND::NT_FP_IS_NEG, H::Op::FP_IS_NEGATIVE},
        {NODE_KIND::NT_FP_IS_POS, H::Op::FP_IS_POSITIVE},
        {NODE_KIND::NT_FP_TO_REAL, H::Op::FP_TO_REAL},
        {NODE_KIND::NT_FP_TO_IEEE_BV, H::Op::FP_TO_IEEE_BV},
        {NODE_KIND::NT_FP_IS_NORMAL, H::Op::FP_IS_NORMAL},
        {NODE_KIND::NT_FP_IS_SUBNORMAL, H::Op::FP_IS_SUBNORMAL},
        {NODE_KIND::NT_FP_IS_ZERO, H::Op::FP_IS_ZERO},
        {NODE_KIND::NT_FP_IS_NAN, H::Op::FP_IS_NAN},
    };
    return t;
}

} // namespace

bool ParserToHir::liftSort(const std::shared_ptr<Sort>& s, H::Sort& out,
                           Uir::Diagnostics& diagnostics) {
    if (!s) {
        diagnostics.error(ErrorCode::E_INTERNAL, "a node has no sort");
        return false;
    }
    if (s->isBool()) { out = H::Sort::boolean(); return true; }
    // IntOrReal is the sort a numeric literal carries. It is Int as far as the
    // HIR is concerned: the literal is a numeral, and letting it become Real
    // would widen every integer constant in the script.
    if (s->isInt() || s->isIntOrReal()) { out = H::Sort::integer(); return true; }
    if (s->isReal()) { out = H::Sort::real(); return true; }
    if (s->isBv())   { out = H::Sort::bitvec(s->getBitWidth()); return true; }
    if (s->isStr())  { out = H::Sort::string(); return true; }
    if (s->isFp())   {
        out = H::Sort::floating(s->getExponentWidth(), s->getSignificandWidth());
        return true;
    }
    if (s->isRoundingMode()) { out = H::Sort::roundingMode(); return true; }
    if (s->isReg())  { out = H::Sort::regLan(); return true; }
    if (s->isArray()) {
        H::Sort index, elem;
        if (!liftSort(s->getIndexSort(), index, diagnostics)) { return false; }
        if (!liftSort(s->getElemSort(), elem, diagnostics)) { return false; }
        out = H::Sort::array(index, elem);
        return true;
    }
    // Sets. All NINE set operators were already in the operator table, and not
    // one of them could ever be reached: a set term needs a set-sorted argument,
    // and this line was missing, so every script that mentioned `(Set T)` failed
    // at its declaration before any operator was looked at. A carefully filled
    // table one line below an unfilled one -- which is why the check that found
    // this asks about the sorts as well as the operators.
    if (s->isSet()) {
        H::Sort elem;
        if (!liftSort(s->getElemSort(), elem, diagnostics)) { return false; }
        out = H::Sort::set(elem);
        return true;
    }
    // Tuples, and the same shape one line further on: the engine carried five
    // tuple NODE_KINDs, their builders and their printer, and this line was
    // missing -- so `(declare-fun x () (Tuple Int Bool))` failed at the
    // declaration and not one of the five was ever reached. An operator table
    // is only as reachable as the sort table under it (CLAUDE.md §6).
    //
    // The nullary case is `UnitTuple`, with no fields, and it is a real sort
    // rather than a malformed one -- so there is no emptiness check here.
    if (s->isTuple()) {
        std::vector<H::Sort> fields;
        fields.reserve(s->getChildrenSize());
        for (size_t i = 0; i < s->getChildrenSize(); ++i) {
            H::Sort f;
            if (!liftSort(s->getChild(i), f, diagnostics)) { return false; }
            fields.push_back(std::move(f));
        }
        out = H::Sort::tuple(std::move(fields));
        return true;
    }
    // A datatype is identified by its NAME: the constructors live in
    // ConstraintModel::datatypes, not in the sort, so a Sort value stays small
    // enough to copy and compare (hir.h, SortKind::DATATYPE). The declaration
    // itself is carried across by lift(), below.
    if (s->isDatatype()) {
        if (s->name.empty()) {
            diagnostics.error(ErrorCode::E_INTERNAL, "a datatype sort has no name");
            return false;
        }
        // A PARAMETRIC datatype applied to arguments is `(L Int)`, and the
        // arguments are part of the sort: dropping them made every instance the
        // same sort, so a selector's result no longer matched what the
        // expression recorded and the whole script failed as an internal error.
        if (!s->children.empty()) {
            std::vector<H::Sort> args;
            for (const auto& ch : s->children) {
                H::Sort a;
                if (!liftSort(ch, a, diagnostics)) { return false; }
                args.push_back(std::move(a));
            }
            out = H::Sort::datatype(s->name, std::move(args));
            return true;
        }
        out = H::Sort::datatype(s->name);
        return true;
    }
    // Uninterpreted sorts are what CHC's predicates range over in the ADT and
    // uninterpreted tracks, and what TPTP's universe is.
    if (s->isDec()) {
        // `(declare-sort S 1)` declares a sort CONSTRUCTOR, and `(S Bool)` is
        // one of its values. The arguments are carried across rather than
        // dropped: flattening the application to the constructor's NAME is what
        // this did before, and it merged `(S Bool)` with `(S Int)`, so two
        // variables of different sorts became comparable and the emitted script
        // declared a sort the source never had. It read back, which is why it
        // went unnoticed.
        //
        // `s->name` and not `s->toString()`: the printed form of an applied
        // constructor is `(S Bool)`, and using it as the HIR name would put the
        // arguments inside the name and then print them twice.
        if (s->children.empty()) {
            out = H::Sort::uninterpreted(s->name);
            return true;
        }
        std::vector<H::Sort> args;
        args.reserve(s->children.size());
        for (const auto& c : s->children) {
            H::Sort a;
            if (!liftSort(c, a, diagnostics)) { return false; }
            args.push_back(std::move(a));
        }
        out = H::Sort::sortApp(s->name, std::move(args));
        return true;
    }
    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                      "sort '" + s->toString() + "' has no HIR counterpart");
    return false;
}

Uir::Hir::ExprPtr ParserToHir::liftConst(const std::shared_ptr<DAGNode>& n,
                                         Uir::Diagnostics& diagnostics) {
    if (n->isCBool()) {
        return H::mkBool(n->getKind() == NODE_KIND::NT_CONST_TRUE);
    }
    // Integer before real: isCInt and isCReal both accept IntOrReal, so asking
    // in the other order would turn every integer literal into a rational.
    if (n->isCInt()) { return H::mkInt(n->toString()); }
    if (n->isCReal()) { return H::mkReal(n->toString()); }
    if (n->isCBV()) {
        H::Sort s;
        if (!liftSort(n->getSort(), s, diagnostics)) { return nullptr; }
        return H::mkBitVec(n->toString(), s.width);
    }
    if (n->isCStr()) { return H::mkString(n->toString()); }
    // A rounding mode is a constant of its own sort, not a symbol. It reaches
    // here as the first child of every rounded floating-point operator, so
    // without it fp.add and its four siblings cannot be lifted at all.
    if (n->isCRoundingMode()) { return H::mkRoundingMode(n->toString()); }
    // A floating-point literal, through dumpSMTLIB2 rather than toString().
    //
    // toString() is the node's NAME, and for the bit-triple form that name is
    // the placeholder `(fp_bit_representation)` with the three bit-vectors
    // hanging off it as children -- only the recursive printer reassembles
    // them. Lifting the name therefore stored a literal that had lost its own
    // value, and since no spelling the engine produces is a decimal, NO
    // floating-point literal could be lifted at all: `(fp #b0 ...)`, `(_ NaN 8
    // 24)` and everything `((_ to_fp 8 24) RNE 1.5)` folds to were refused
    // alike. LIT_FLOAT was reachable only from a frontend building one
    // directly, which is why the round trip never showed it.
    if (n->isCFP()) {
        H::Sort s;
        if (!liftSort(n->getSort(), s, diagnostics)) { return nullptr; }
        return H::mkFloat(dumpSMTLIB2(n), s.exponent_bits, s.significand_bits);
    }
    // The three nullary regular expressions and the empty set. The engine makes
    // them CONSTANTS, not zero-argument operators, and so does the HIR -- mkOp
    // refuses an empty argument list, which is why they are literals on both
    // sides (hir.h, ExprKind::LIT_REGLAN and LIT_SET). Being constants is also
    // why they were not found by the operator-table diff that turned up the
    // rest of the regex cluster: they were never going to be table entries.
    // Selected by SORT, not by kind: mkConstReg builds these as an ordinary
    // NT_CONST carrying the name, so `n->getKind()` is NT_CONST and only the
    // sort says what it is. Checking the kind looked right and matched nothing.
    if (n->getSort() && n->getSort()->isReg()) {
        return H::mkReglanConst(n->toString());
    }
    if (n->getKind() == NODE_KIND::NT_SET_EMPTY) {
        // Sort-annotated: `(as set.empty (Set T))`. The element sort is
        // derivable from nothing else on the term.
        H::Sort s;
        if (!liftSort(n->getSort(), s, diagnostics)) { return nullptr; }
        return H::mkSetConst("set.empty", s);
    }
    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                      "constant '" + n->toString() + "' has no HIR counterpart");
    return nullptr;
}

Uir::Hir::ExprPtr ParserToHir::liftNumericChild(
    const std::shared_ptr<DAGNode>& n, const H::Sort* expected,
    Uir::Diagnostics& diagnostics) {
    if (n && n->isConst() && n->getSort() && n->getSort()->isIntOrReal()
        && expected != nullptr) {
        if (expected->kind == H::SortKind::REAL) { return H::mkReal(n->toString()); }
        if (expected->kind == H::SortKind::INT)  { return H::mkInt(n->toString()); }
    }
    auto result = liftExpr(n, diagnostics);
    // HIR has concrete sorts. Preserve SMT-LIB's numeric embedding explicitly,
    // including an entire integer-valued ite used in a Real context. Rebuilding
    // every ite branch recursively both lost sharing and exhausted the stack.
    if (result && expected && expected->kind == H::SortKind::REAL
        && result->sort.kind == H::SortKind::INT) {
        return H::mkOp(H::Op::TO_REAL, {result});
    }
    return result;
}

Uir::Hir::ExprPtr ParserToHir::liftQuantifier(const std::shared_ptr<DAGNode>& n,
                                              Uir::Diagnostics& diagnostics) {
    std::vector<H::Binder> binders;
    // The previous binding for each name, so leaving this scope RESTORES rather
    // than clears. Erasing instead is wrong in a way that only shows up under
    // shadowing: in `(forall ((x Int)) (and (P x) (forall ((x BV8)) (Q x))))`
    // the inner quantifier would erase `x` on the way out, and the outer body's
    // remaining occurrences would then lift as free identifiers of a variable
    // the model never declared.
    std::vector<std::pair<std::string, std::optional<Binding>>> saved;
    for (const auto& v : n->getQuantVars()) {
        H::Sort s;
        if (!liftSort(v->getSort(), s, diagnostics)) { return nullptr; }
        // Quoting changes spelling, not identity: an inner x also shadows an
        // outer |x|. Keep both lookup and alpha-renaming on the same key.
        const std::string src = boundSymbolKey(v->getName());
        const auto prev = bound_.find(src);
        // SMT-LIB permits shadowing and the HIR does not, so an inner binder
        // over a name already in scope is alpha-renamed. The alternative --
        // lifting it unchanged -- produces a model typeCheck rejects, and
        // refusing would make a legal script unsupported.
        // Preserve lexical quoting for a fresh binder (e.g. |true| must not
        // become the Boolean literal true when exported).
        const std::string hir_name = prev == bound_.end()
                && !parser_->getSymbolManager()->hasVar(src)
                && !active_bound_names_.count(src)
            ? v->getName() : freshBoundName(v->getName());
        active_bound_names_.insert(boundSymbolKey(hir_name));
        binders.push_back(H::Binder{hir_name, s});
        saved.emplace_back(src, prev == bound_.end() ? std::nullopt
                                                     : std::optional<Binding>(prev->second));
        bound_[src] = Binding{hir_name, s};
    }
    ++scope_id_;
    H::ExprPtr body = liftExpr(n->getQuantBody(), diagnostics);
    ++scope_id_;
    for (const auto& binder : binders) {
        active_bound_names_.erase(boundSymbolKey(binder.name));
    }
    for (auto it = saved.rbegin(); it != saved.rend(); ++it) {
        if (it->second) { bound_[it->first] = *it->second; }
        else            { bound_.erase(it->first); }
    }
    if (!body) { return nullptr; }
    return n->getKind() == NODE_KIND::NT_FORALL ? H::mkForall(binders, body)
                                                : H::mkExists(binders, body);
}

Uir::Hir::ExprPtr ParserToHir::liftLet(const std::shared_ptr<DAGNode>& n,
                                      Uir::Diagnostics& diagnostics) {
    using Saved = std::pair<const DAGNode*, std::optional<H::ExprPtr>>;
    std::vector<Saved> saved;
    const auto restore = [&]() {
        for (auto it = saved.rbegin(); it != saved.rend(); ++it) {
            if (it->second) { let_values_[it->first] = *it->second; }
            else { let_values_.erase(it->first); }
        }
        ++scope_id_;
    };
    const auto bind_group = [&](const std::vector<std::shared_ptr<DAGNode>>& bindings,
                                std::size_t first) {
        std::vector<std::pair<const DAGNode*, H::ExprPtr>> values;
        values.reserve(bindings.size() - first);
        // A binding list is parallel: every RHS sees the enclosing scope.
        // A later binding list in a let chain sees all earlier lists.
        for (std::size_t i = first; i < bindings.size(); ++i) {
            const auto& binding = bindings[i];
            if (!binding || !binding->isLetBindVar()
                || binding->getChildrenSize() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL, "malformed let binding during HIR lifting");
                return false;
            }
            H::ExprPtr value = liftExpr(binding->getChild(0), diagnostics);
            if (!value) { return false; }
            values.emplace_back(binding.get(), std::move(value));
        }
        for (auto& value : values) {
            const auto previous = let_values_.find(value.first);
            saved.emplace_back(value.first, previous == let_values_.end()
                ? std::nullopt : std::optional<H::ExprPtr>(previous->second));
            let_values_[value.first] = std::move(value.second);
        }
        ++scope_id_;
        return true;
    };
    const std::size_t count = n->getChildrenSize();
    if (count == 0) {
        diagnostics.error(ErrorCode::E_INTERNAL, "let has no body during HIR lifting");
        return nullptr;
    }
    if (n->isLetChain()) {
        for (std::size_t i = 0; i + 1 < count; ++i) {
            const auto& group = n->getChild(i);
            if (!group || !group->isLetBindVarList()) {
                diagnostics.error(ErrorCode::E_INTERNAL, "malformed let chain during HIR lifting");
                restore();
                return nullptr;
            }
            if (!bind_group(group->getChildren(), 0)) { restore(); return nullptr; }
        }
    } else if (!bind_group(n->getChildren(), 1)) {
        restore();
        return nullptr;
    }
    H::ExprPtr body = liftExpr(n->getChild(n->isLetChain() ? count - 1 : 0), diagnostics);
    restore();
    return body;
}

Uir::Hir::ExprPtr ParserToHir::liftExpr(const std::shared_ptr<DAGNode>& n,
                                        Uir::Diagnostics& diagnostics) {
    // Ordinary DAG operands are scheduled bottom-up. Binder and let handlers
    // retain ownership of their environments and enter this worklist for each
    // body/RHS, so a cache made outside a scope cannot capture its variables.
    struct Pending {
        std::shared_ptr<DAGNode> node;
        std::size_t next_argument = 0;
    };
    std::vector<Pending> pending{{n}};
    std::unordered_set<const DAGNode*> active;
    if (n) { active.insert(n.get()); }
    H::ExprPtr result;
    while (!pending.empty()) {
        auto& frame = pending.back();
        const auto node = frame.node;
        if (node) {
            const auto cached = memo_.find({node.get(), scope_id_});
            if (cached != memo_.end()) {
                result = cached->second;
                active.erase(node.get());
                pending.pop_back();
                continue;
            }
        }
        const bool scoped = node && (node->isLet() || node->isLetChain()
            || node->getKind() == NODE_KIND::NT_FORALL
            || node->getKind() == NODE_KIND::NT_EXISTS);
        const bool captured_let = node && node->isLetBindVar()
            && let_values_.find(node.get()) != let_values_.end();
        const bool ordinary = node && (!node->isConst() || symbolicFpConstructor(node))
            && !scoped && !captured_let
            && (!node->isVar() || node->isLetBindVar())
            && node->getKind() != NODE_KIND::NT_FUNC_PARAM;
        if (ordinary && frame.next_argument < node->getChildrenSize()) {
            const auto index = frame.next_argument++;
            // Defined applications carry a function declaration at child zero;
            // it is metadata, not an operand in the calling environment.
            if (index == 0 && (node->getKind() == NODE_KIND::NT_FUNC_APPLY
                              || node->getKind() == NODE_KIND::NT_FUNC_REC_APPLY)) {
                continue;
            }
            const auto child = node->getChild(index);
            if (child && memo_.find({child.get(), scope_id_}) != memo_.end()) { continue; }
            if (child && !active.insert(child.get()).second) {
                diagnostics.error(ErrorCode::E_INTERNAL, "cyclic parser expression reached HIR lifting");
                return nullptr;
            }
            pending.push_back({child});
            continue;
        }
        result = liftExprUncached(node, diagnostics);
        if (!result) { return nullptr; }
        if (node) {
            // A binder/let handler may advance the epoch before restoring its
            // enclosing environment. Cache the completed node in that restored
            // environment too, so the enclosing worklist consumes it once.
            memo_[{node.get(), scope_id_}] = result;
            active.erase(node.get());
        }
        pending.pop_back();
    }
    return result;
}

Uir::Hir::ExprPtr ParserToHir::liftExprUncached(const std::shared_ptr<DAGNode>& n,
                                                Uir::Diagnostics& diagnostics) {
    if (!n) {
        diagnostics.error(ErrorCode::E_INTERNAL, "liftExpr: null node");
        return nullptr;
    }
    // The memo. Not an optimisation: the input is a hash-consed DAG, so a
    // shared subterm is literally the same pointer on every path that reaches
    // it, and a walk without this is exponential in the sharing.
    //
    // Deliberately NOT consulted for quantifiers below -- see there.
    const auto key = std::make_pair(n.get(), scope_id_);
    const auto it = memo_.find(key);
    if (it != memo_.end()) { return it->second; }

    H::ExprPtr result;

    if (symbolicFpConstructor(n)) {
        // The native DAG stores every (fp sign exponent fraction) as NT_CONST,
        // even when its BV fields are expressions. Preserve those operands as
        // a shared HIR DAG; a float literal's text cannot contain variables.
        H::Sort format;
        if (!liftSort(n->getSort(), format, diagnostics)) { return nullptr; }
        std::vector<H::ExprPtr> bits;
        for (const auto& child : n->getChildren()) {
            auto field = liftExpr(child, diagnostics);
            if (!field) { return nullptr; }
            bits.push_back(std::move(field));
        }
        auto pattern = H::mkOp(H::Op::BV_CONCAT, {bits[0],
            H::mkOp(H::Op::BV_CONCAT, {bits[1], bits[2]})});
        result = H::mkIeeeBvToFp(pattern, format.exponent_bits, format.significand_bits);
    } else if (n->isConst()) {
        result = liftConst(n, diagnostics);
    } else if (n->getKind() == NODE_KIND::NT_FORALL
               || n->getKind() == NODE_KIND::NT_EXISTS) {
        // Not memoised. The lift of a body depends on which binders are in
        // scope, and the same DAGNode can appear under different scopes, so a
        // memo entry made under one scope would be reused under another.
        return liftQuantifier(n, diagnostics);
    } else if (n->isLet() || n->isLetChain()) {
        // `(let ((x e)) body)`. SMT-LIB's let is a MACRO -- the standard defines
        // it by substitution -- so inlining is exact and the HIR needs no let
        // of its own.
        //
        // Capture RHS values in their lexical scope before lifting the body.
        // Deferring them until a reference is encountered would let an inner
        // quantifier capture same-named variables from the RHS.
        //
        // What inlining costs is SIZE, not meaning: a value bound once and used
        // three times is written three times in the emitted text. In memory it
        // is one node -- the memo returns the same ExprPtr -- so the HIR itself
        // stays a DAG.
        result = liftLet(n, diagnostics);
        if (!result) { return nullptr; }
    } else if (n->getKind() == NODE_KIND::NT_LET_BIND_VAR) {
        // A reference to a let-bound name: its VALUE, which is child 0.
        //
        // Checked before isVar(), which includes isLetBindVar(). Falling into
        // that branch produced `mkIdent(name, sort)` -- an identifier the model
        // never declares -- so the whole `let` silently became a reference to
        // nothing. typeCheck rejects it, which is the only reason it was not
        // shipped as a wrong answer.
        const auto captured = let_values_.find(n.get());
        result = captured != let_values_.end() ? captured->second
                                               : liftExpr(n->getChild(0), diagnostics);
        if (!result) { return nullptr; }
    } else if (n->isVar() || n->getKind() == NODE_KIND::NT_FUNC_PARAM) {
        // NT_FUNC_PARAM is how a define-fun's BODY refers to its parameters,
        // and it is not an isVar() kind -- so without it the body lifted its
        // own parameters as "'func_param' has no HIR counterpart". It resolves
        // through the same bound_ map a quantifier binder does, because in the
        // defining axiom that is exactly what it has become.
        const auto b = bound_.find(boundSymbolKey(n->getName()));
        if (b != bound_.end()) {
            // BOUND_VAR, not IDENT. The HIR draws the distinction deliberately:
            // a bound variable is not a free variable of the model, and an
            // IDENT here would be reported by features() and made eligible for
            // the bound-ints pass to put bounds on -- bounds on a variable the
            // model does not own. typeCheck rejects it outright, which is how
            // this was caught rather than shipped.
            result = H::mkBoundVar(b->second.hir_name, b->second.sort);
        } else {
            H::Sort s;
            if (!liftSort(n->getSort(), s, diagnostics)) { return nullptr; }
            result = H::mkIdent(n->getName(), s);
        }
    } else if (n->isUFApplication() || n->getKind() == NODE_KIND::NT_FUNC_APPLY
               || n->getKind() == NODE_KIND::NT_FUNC_REC_APPLY) {
        // An uninterpreted function application. Its result sort is the
        // function's, which the node already carries.
        H::Sort s;
        if (!liftSort(n->getSort(), s, diagnostics)) { return nullptr; }
        // The applied symbol is the NODE's own name, and every child is an
        // argument -- createNode(sort, NT_UF_APPLY, name, args). Reading child
        // 0 as the symbol instead makes `(f c)` an application of `c`, which
        // typeCheck reports as an undeclared function and which would otherwise
        // have emitted a script applying the wrong name.
        //
        // NT_FUNC_APPLY -- the application of a `define-fun` -- takes the same
        // path, and its body is carried across separately as a defining axiom
        // (see lift()). It used to fail with "'func_apply' has no HIR
        // counterpart" on three of this repository's own test instances.
        //
        // **Its child layout is not the same.** mkApplyFunc puts the FUNCTION
        // at child 0 and the arguments after it, while NT_UF_APPLY's children
        // are all arguments -- so the first argument here starts at index 1.
        // Reading from 0 lifts the function node itself and fails as
        // "'func_def' has no HIR counterpart", which is how the difference
        // announced itself; had NT_FUNC_DEF been liftable it would instead have
        // produced an application with one extra argument.
        const std::size_t first =
            (n->getKind() == NODE_KIND::NT_FUNC_APPLY
             || n->getKind() == NODE_KIND::NT_FUNC_REC_APPLY) ? 1u : 0u;
        std::vector<H::ExprPtr> args;
        const std::vector<std::shared_ptr<DAGNode>> params =
            first == 1 && n->getChild(0) ? n->getChild(0)->getFuncParams()
                                         : std::vector<std::shared_ptr<DAGNode>>{};
        for (std::size_t i = first; i < n->getChildrenSize(); ++i) {
            H::Sort expected;
            const H::Sort* want = nullptr;
            const std::size_t param = i - first;
            if (param < params.size()
                && liftSort(params[param]->getSort(), expected, diagnostics)) {
                want = &expected;
            }
            H::ExprPtr a = liftNumericChild(n->getChild(i), want, diagnostics);
            if (!a) { return nullptr; }
            args.push_back(std::move(a));
        }
        result = H::mkApply(n->getName(), s, args);
    } else if (n->getKind() == NODE_KIND::NT_REG_NONE
               || n->getKind() == NODE_KIND::NT_REG_ALL
               || n->getKind() == NODE_KIND::NT_REG_ALLCHAR) {
        // The three nullary regular expressions. Literals rather than
        // zero-argument operators because mkOp refuses an empty argument list
        // (hir.h, ExprKind::LIT_REGLAN), so they cannot be table entries.
        result = H::mkReglanConst(kindToString(n->getKind()));
    } else if (n->getKind() == NODE_KIND::NT_SET_EMPTY) {
        // `(as set.empty (Set T))` -- sort-annotated, because the element sort
        // is derivable from nothing else. Same reason it is a literal.
        H::Sort es;
        if (!liftSort(n->getSort(), es, diagnostics)) { return nullptr; }
        result = H::mkSetConst("set.empty", es);
    } else if (n->getKind() == NODE_KIND::NT_TUPLE_UNIT) {
        // `tuple.unit`. A literal on both sides, for the reason the nullary
        // regular expressions are: it takes no arguments and mkOp refuses an
        // empty argument list. Unlike set.empty it needs no sort annotation --
        // UnitTuple is the only sort it can have.
        result = H::mkTupleUnit();
    } else if (n->getKind() == NODE_KIND::NT_TUPLE_SELECT
               || n->getKind() == NODE_KIND::NT_TUPLE_UPDATE
               || n->getKind() == NODE_KIND::NT_TUPLE_PROJECT) {
        // Indexed, and so not table entries, for the reason given at the
        // bit-vector branch below: the engine stores an index as a constant
        // CHILD and the HIR keeps it in Expr::indices.
        //
        // The three do not agree on WHICH children are indices, and that is
        // the part worth being explicit about. tuple.select is (t, i);
        // tuple.update is (t, i, v) -- the index sits BETWEEN the two terms,
        // so a loop that took "everything after the first child" as indices
        // would make the replacement value an index; tuple.project is
        // (t, i1 ... ik), where everything after the first child really is.
        const std::size_t n_children = n->getChildrenSize();
        if (n_children < 1) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "'" + kindToString(n->getKind())
                                  + "' has no arguments");
            return nullptr;
        }
        H::ExprPtr tuple = liftExpr(n->getChild(0), diagnostics);
        if (!tuple) { return nullptr; }
        const std::size_t idx_lo = 1;
        const std::size_t idx_hi = (n->getKind() == NODE_KIND::NT_TUPLE_UPDATE)
                                       ? std::min<std::size_t>(2, n_children)
                                       : n_children;
        std::vector<unsigned> idx;
        for (std::size_t i = idx_lo; i < idx_hi; ++i) {
            const std::shared_ptr<DAGNode>& c = n->getChild(i);
            if (!c->isCInt()) {
                // The engine's own builders refuse a non-constant index, so
                // reaching this is a broken invariant and not a bad input.
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "index " + std::to_string(i) + " of '"
                                      + kindToString(n->getKind())
                                      + "' is not a constant integer");
                return nullptr;
            }
            idx.push_back(static_cast<unsigned>(std::stoul(c->toString())));
        }
        if (n->getKind() == NODE_KIND::NT_TUPLE_PROJECT) {
            result = H::mkTupleProject(tuple, std::move(idx));
        } else if (idx.size() != 1) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "'" + kindToString(n->getKind())
                                  + "' needs one index, got "
                                  + std::to_string(idx.size()));
            return nullptr;
        } else if (n->getKind() == NODE_KIND::NT_TUPLE_SELECT) {
            result = H::mkTupleSelect(tuple, idx[0]);
        } else {
            if (n_children < 3) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "'tuple.update' needs a tuple, an index and "
                                  "a value");
                return nullptr;
            }
            H::ExprPtr value = liftExpr(n->getChild(2), diagnostics);
            if (!value) { return nullptr; }
            result = H::mkTupleUpdate(tuple, idx[0], value);
        }
    } else if (n->getKind() == NODE_KIND::NT_INT_TO_BV
               || n->getKind() == NODE_KIND::NT_NAT_TO_BV) {
        // `(_ int2bv w) n`. The width is the RESULT sort's, not a child: the
        // engine puts it in the sort it built the node with, so there is no
        // index child to read -- which is why this needs its own branch rather
        // than the indexed one below.
        H::ExprPtr arg = liftExpr(n->getChild(0), diagnostics);
        if (!arg) { return nullptr; }
        H::Sort bs;
        if (!liftSort(n->getSort(), bs, diagnostics)) { return nullptr; }
        if (bs.kind != H::SortKind::BITVEC) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "int2bv produced a non-bit-vector sort");
            return nullptr;
        }
        result = H::mkIntToBv(arg, bs.width);
    } else if (n->getKind() == NODE_KIND::NT_FP_TO_SBV
               || n->getKind() == NODE_KIND::NT_FP_TO_UBV) {
        // `((_ fp.to_sbv w) rm x)`. The engine builds this as THREE children --
        // rounding mode, value, and the width as a constant node
        // (op_parser.cpp, mkFpToUbv) -- while the HIR takes two arguments and
        // an index. So the third child is dropped here, not lifted: it is the
        // index, and lifting it would make the width an argument.
        //
        // The width is read from the RESULT sort rather than from that child,
        // because the sort is what the engine actually computed the node with
        // and the two cannot disagree.
        if (n->getChildrenSize() < 2) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "fp.to_sbv/fp.to_ubv needs a rounding mode and a value");
            return nullptr;
        }
        H::ExprPtr rm = liftExpr(n->getChild(0), diagnostics);
        if (!rm) { return nullptr; }
        H::ExprPtr x = liftExpr(n->getChild(1), diagnostics);
        if (!x) { return nullptr; }
        H::Sort bs;
        if (!liftSort(n->getSort(), bs, diagnostics)) { return nullptr; }
        if (bs.kind != H::SortKind::BITVEC) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "fp.to_sbv/fp.to_ubv produced a non-bit-vector sort");
            return nullptr;
        }
        result = H::mkFpToBv(n->getKind() == NODE_KIND::NT_FP_TO_SBV ? H::Op::FP_TO_SBV
                                                                    : H::Op::FP_TO_UBV,
                             rm, x, bs.width);
    } else if (n->getKind() == NODE_KIND::NT_DT_CONSTRUCTOR
               || n->getKind() == NODE_KIND::NT_DT_SELECTOR
               || n->getKind() == NODE_KIND::NT_DT_TESTER) {
        // The three datatype applications. They are not operator-table entries
        // because none of them is an operator: each names a constructor or a
        // field the MODEL declared, so the name is part of the term and the HIR
        // has an ExprKind rather than an Op for it.
        H::Sort s;
        if (!liftSort(n->getSort(), s, diagnostics)) { return nullptr; }
        std::vector<H::ExprPtr> args;
        args.reserve(n->getChildrenSize());
        for (std::size_t i = 0; i < n->getChildrenSize(); ++i) {
            H::ExprPtr a = liftExpr(n->getChild(i), diagnostics);
            if (!a) { return nullptr; }
            args.push_back(std::move(a));
        }
        const std::string name = n->getName();
        if (n->getKind() == NODE_KIND::NT_DT_CONSTRUCTOR) {
            result = H::mkDtConstructor(name, s, std::move(args));
        } else if (args.size() != 1) {
            // A selector and a tester each take exactly the value they inspect.
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "'" + name + "' takes one argument, not "
                                  + std::to_string(args.size()));
            return nullptr;
        } else if (n->getKind() == NODE_KIND::NT_DT_SELECTOR) {
            result = H::mkDtSelector(name, s, args[0]);
        } else {
            // The engine names a tester `is-<ctor>` and the HIR carries the bare
            // CONSTRUCTOR name, because that is what the source formats write --
            // hir_to_parser puts the prefix back. Lifting the engine's spelling
            // unchanged would round-trip as `is-is-cons`.
            if (name.rfind("is-", 0) != 0) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "tester '" + name + "' is not spelled is-<constructor>");
                return nullptr;
            }
            result = H::mkDtTester(name.substr(3), args[0]);
        }
    } else if (n->getKind() == NODE_KIND::NT_CONST_ARRAY) {
        // `((as const (Array T U)) v)`. Indexed by the RESULT SORT, like
        // int2bv: the value fixes U and says nothing about T, so the sort is
        // where the array's identity lives and the child is only the value.
        if (n->getChildrenSize() != 1) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "a constant array has "
                                  + std::to_string(n->getChildrenSize())
                                  + " children, expected 1");
            return nullptr;
        }
        H::Sort as;
        if (!liftSort(n->getSort(), as, diagnostics)) { return nullptr; }
        H::ExprPtr v = liftExpr(n->getChild(0), diagnostics);
        if (!v) { return nullptr; }
        result = H::mkConstArray(as, v);
    } else if (n->getKind() == NODE_KIND::NT_IS_DIVISIBLE) {
        // `((_ divisible n) t)`. The engine keeps n as child 1 rather than as
        // an index -- it accepts a flat `(is_divisible t n)` too, and both
        // spellings build the same node -- so the divisor moves into the HIR's
        // `indices` here.
        if (n->getChildrenSize() != 2) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "divisible has " + std::to_string(n->getChildrenSize())
                                  + " children, expected 2");
            return nullptr;
        }
        const std::shared_ptr<DAGNode>& by = n->getChild(1);
        if (!by->isCInt()) {
            // The engine permits a VARIABLE divisor as an extension. SMT-LIB
            // does not -- an index is a numeral -- and the HIR follows SMT-LIB,
            // so this is refused by name rather than lifted as if the divisor
            // were constant, which would fix it at whatever value happened to
            // be there and answer a different question.
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "'divisible' by a non-constant divisor is an "
                              "extension of SMT-LIB, whose index must be a "
                              "numeral, and the HIR has no operator for it");
            return nullptr;
        }
        H::ExprPtr t = liftExpr(n->getChild(0), diagnostics);
        if (!t) { return nullptr; }
        result = H::mkIsDivisible(
            t, static_cast<unsigned>(std::stoul(by->toString())));
    } else if (n->getKind() == NODE_KIND::NT_FP_TO_FP
               || n->getKind() == NODE_KIND::NT_FP_TO_FP_UNSIGNED) {
        // `((_ to_fp eb sb) rm x)`. The engine keeps eb and sb as children 0
        // and 1 -- unlike int2bv, where the width lives only in the sort -- so
        // this reads FOUR children and lifts the last two.
        //
        // The format still comes from the result sort rather than from those
        // two children: the sort is what the engine computed the node with, the
        // HIR indexes the operator by it, and if the two ever disagreed the
        // sort is the one the rest of the term was checked against.
        if (n->getChildrenSize() == 3 && n->getKind() == NODE_KIND::NT_FP_TO_FP) {
            // `((_ to_fp eb sb) bv)` with no rounding mode is not a
            // conversion: it REINTERPRETS a bit pattern as a float, the
            // inverse of fp.to_ieee_bv, with its own HIR operator -- the
            // rounding form would answer a different question on every
            // input, since rounding a bit pattern read as an integer is not
            // reading it as a float.
            H::ExprPtr bv = liftExpr(n->getChild(2), diagnostics);
            if (!bv) { return nullptr; }
            H::Sort fs;
            if (!liftSort(n->getSort(), fs, diagnostics)) { return nullptr; }
            if (fs.kind != H::SortKind::FLOAT) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "to_fp produced a non-floating-point sort");
                return nullptr;
            }
            result = H::mkIeeeBvToFp(bv, fs.exponent_bits, fs.significand_bits);
        } else if (n->getChildrenSize() != 4) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "to_fp has " + std::to_string(n->getChildrenSize())
                                  + " children, expected 4");
            return nullptr;
        } else {
        H::ExprPtr rm = liftExpr(n->getChild(2), diagnostics);
        if (!rm) { return nullptr; }
        const auto& operand = n->getChild(3);
        // SMT-LIB has no Int-to-FP overload. A numeral in the numeric overload
        // is Real even when the native DAG's overloaded numeral looks integer.
        // Constant rounding modes used to hide this gap by folding to a float.
        const H::Sort real = H::Sort::real();
        H::ExprPtr x = n->getKind() == NODE_KIND::NT_FP_TO_FP && operand->isCInt()
            ? H::mkReal(operand->toString())
            : n->getKind() == NODE_KIND::NT_FP_TO_FP && operand->getSort()->isIntOrReal()
                ? liftNumericChild(operand, &real, diagnostics)
                : liftExpr(operand, diagnostics);
        if (!x) { return nullptr; }
        H::Sort fs;
        if (!liftSort(n->getSort(), fs, diagnostics)) { return nullptr; }
        if (fs.kind != H::SortKind::FLOAT) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "to_fp produced a non-floating-point sort");
            return nullptr;
        }
        result = H::mkToFp(n->getKind() == NODE_KIND::NT_FP_TO_FP
                               ? H::Op::TO_FP : H::Op::TO_FP_UNSIGNED,
                           rm, x, fs.exponent_bits, fs.significand_bits);
        }
    } else if (n->getKind() == NODE_KIND::NT_BV_EXTRACT
               || n->getKind() == NODE_KIND::NT_BV_ZERO_EXT
               || n->getKind() == NODE_KIND::NT_BV_SIGN_EXT
               || n->getKind() == NODE_KIND::NT_BV_ROTATE_LEFT
               || n->getKind() == NODE_KIND::NT_BV_ROTATE_RIGHT
               || n->getKind() == NODE_KIND::NT_BV_REPEAT
               || n->getKind() == NODE_KIND::NT_REG_LOOP) {
        // Indexed operators, and the reason they are not table entries: the two
        // sides store the indices differently. The engine makes them ordinary
        // constant CHILDREN; the HIR keeps them in `Expr::indices`, because
        // they say WHICH function is applied rather than what it is applied to
        // (hir.h). So the lift has to move children into indices, and a table
        // mapping kind to Op has nowhere to express that -- which is why these
        // three were missing while every non-indexed BV operator was present.
        H::ExprPtr arg = liftExpr(n->getChild(0), diagnostics);
        if (!arg) { return nullptr; }
        std::vector<unsigned> idx;
        for (std::size_t i = 1; i < n->getChildrenSize(); ++i) {
            const std::shared_ptr<DAGNode>& c = n->getChild(i);
            if (!c->isCInt()) {
                // The engine's own builders refuse a non-constant index, so
                // this is a broken invariant rather than a bad input.
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "index " + std::to_string(i) + " of '"
                                      + kindToString(n->getKind())
                                      + "' is not a constant integer");
                return nullptr;
            }
            // Through the decimal text, the way liftConst reads every other
            // integer constant: the engine's Number is GMP-backed and its
            // toString is the authoritative spelling.
            idx.push_back(static_cast<unsigned>(std::stoul(c->toString())));
        }
        if (n->getKind() == NODE_KIND::NT_REG_LOOP) {
            if (idx.size() != 2) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "re.loop needs two indices, got "
                                      + std::to_string(idx.size()));
                return nullptr;
            }
            result = H::mkReLoop(arg, idx[0], idx[1]);
        } else if (n->getKind() == NODE_KIND::NT_BV_EXTRACT) {
            if (idx.size() != 2) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "extract needs two indices, got "
                                      + std::to_string(idx.size()));
                return nullptr;
            }
            result = H::mkBvExtract(arg, idx[0], idx[1]);
        } else {
            if (idx.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "a one-index bit-vector operator needs one "
                                  "index, got " + std::to_string(idx.size()));
                return nullptr;
            }
            switch (n->getKind()) {
            case NODE_KIND::NT_BV_ROTATE_LEFT:
                result = H::mkBvRotate(H::Op::BV_ROTATE_LEFT, arg, idx[0]);
                break;
            case NODE_KIND::NT_BV_ROTATE_RIGHT:
                result = H::mkBvRotate(H::Op::BV_ROTATE_RIGHT, arg, idx[0]);
                break;
            case NODE_KIND::NT_BV_REPEAT:
                result = H::mkBvRepeat(arg, idx[0]);
                break;
            default:
                result = H::mkBvExtend(n->getKind() == NODE_KIND::NT_BV_ZERO_EXT
                                           ? H::Op::BV_ZERO_EXTEND
                                           : H::Op::BV_SIGN_EXTEND,
                                       arg, idx[0]);
                break;
            }
        }
    } else {
        const auto op = opTable().find(n->getKind());
        if (op == opTable().end()) {
            // Named, never dropped. A lift that skipped what it did not know
            // would hand back a smaller model that type-checks and answers a
            // different question -- and report success.
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "'" + kindToString(n->getKind())
                                  + "' has no HIR counterpart, so this term cannot be "
                                    "lifted; skipping it would silently drop a constraint");
            return nullptr;
        }
        H::Sort parent_sort;
        if (!liftSort(n->getSort(), parent_sort, diagnostics)) { return nullptr; }
        // The native ite may keep the first branch's overloaded numeral
        // sort. Its already-lifted value branches resolve that ambiguity; an
        // Int branch is then explicitly embedded in Real by liftNumericChild.
        if (op->second == H::Op::ITE && n->getChildrenSize() == 3
            && (parent_sort.kind == H::SortKind::INT || parent_sort.kind == H::SortKind::REAL)) {
            for (std::size_t i = 1; i < 3; ++i) {
                const auto branch = memo_.find({n->getChild(i).get(), scope_id_});
                if (branch != memo_.end() && branch->second->sort.kind == H::SortKind::REAL) {
                    parent_sort = H::Sort::real();
                }
            }
        }
        H::Sort compared_sort;
        const H::Sort* compared = nullptr;
        if (op->second == H::Op::EQ || op->second == H::Op::DISTINCT
            || op->second == H::Op::LE || op->second == H::Op::LT
            || op->second == H::Op::GE || op->second == H::Op::GT) {
            bool saw_int = false;
            for (std::size_t i = 0; i < n->getChildrenSize(); ++i) {
                const auto& sort = n->getChild(i)->getSort();
                if (!sort) { continue; }
                const auto lifted = memo_.find({n->getChild(i).get(), scope_id_});
                const bool lifted_real = lifted != memo_.end()
                    && lifted->second->sort.kind == H::SortKind::REAL;
                if (sort->isReal() || lifted_real) {
                    compared_sort = H::Sort::real();
                    compared = &compared_sort;
                    break;
                }
                saw_int = saw_int || sort->isInt();
            }
            if (compared == nullptr && saw_int) {
                compared_sort = H::Sort::integer();
                compared = &compared_sort;
            }
        }
        std::vector<H::ExprPtr> args;
        for (std::size_t i = 0; i < n->getChildrenSize(); ++i) {
            const H::Sort* expected = nullptr;
            if (op->second == H::Op::TO_REAL) {
                static const H::Sort integer = H::Sort::integer();
                expected = &integer;
            } else if (op->second == H::Op::TO_INT || op->second == H::Op::IS_INT) {
                static const H::Sort real = H::Sort::real();
                expected = &real;
            } else if (compared != nullptr) {
                expected = compared;
            } else if ((parent_sort.kind == H::SortKind::INT
                        || parent_sort.kind == H::SortKind::REAL)
                       && !(op->second == H::Op::ITE && i == 0)) {
                expected = &parent_sort;
            }
            H::ExprPtr a = liftNumericChild(n->getChild(i), expected, diagnostics);
            if (!a) { return nullptr; }
            args.push_back(std::move(a));
        }
        if (args.empty()) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "'" + kindToString(n->getKind()) + "' has no arguments");
            return nullptr;
        }
        result = mkNary(op->second, std::move(args), diagnostics);
        if (!result) { return nullptr; }
    }

    if (result) { memo_[key] = result; }
    return result;
}

bool ParserToHir::isDatatypeMember(const std::string& name) const {
    return datatype_members_.count(name) != 0;
}

bool ParserToHir::lift(H::ConstraintModel& out, Uir::Diagnostics& diagnostics) {
    return lift(out, diagnostics, false);
}

bool ParserToHir::lift(H::ConstraintModel& out, Uir::Diagnostics& diagnostics,
                       bool retain_nonrecursive_definitions) {
    // Datatypes first, and in DECLARATION order: a variable's sort, a
    // selector's field sort or another datatype's constructor may name one, so
    // the declarations have to be in the model before anything that mentions
    // them. The engine keeps that order in the SymbolManager, which is the same
    // reason dumpSMT2 walks it.
    //
    // The constructors are read off the SORT rather than rebuilt from the
    // declared functions: `(declare-datatypes ...)` registers a declare-fun for
    // every constructor, selector and tester as well, and lifting those as
    // ordinary uninterpreted functions would declare each of them twice --
    // once in the datatype and once beside it -- in a script that then refuses
    // itself as a redeclaration.
    std::unordered_set<std::string> lifted_free_sort_names;
    for (const std::string& sort_name : parser_->getSymbolManager()->getSortOrder()) {
        const auto& sort_map = parser_->getSymbolManager()->getSortKeyMap();
        const auto it = sort_map.find(sort_name);
        if (it == sort_map.end() || !it->second) { continue; }
        const std::shared_ptr<Sort>& s = it->second;
        // Preserve explicit free constructors even when no declaration or
        // constraint refers to them. Sort aliases (SK_DEF) and datatype
        // constructors (SK_DATATYPE) are deliberately not free declarations.
        // Type parameters are absent from the live map once their declaration
        // scope closes. Aliases can point at the same SK_DEC (including an
        // instantiated constructor), so only its canonical key is a free
        // constructor; getSortOrder may retain/repeat keys after temporary
        // registrations, hence the explicit deduplication.
        if (s->isDec() && sort_name == s->name
            && lifted_free_sort_names.insert(sort_name).second) {
            out.uninterpreted_sorts.push_back(
                H::UninterpretedSortDecl{sort_name, s->arity, {}});
            continue;
        }
        if (!s->isDatatype() || s->name != sort_name || !s->hasDtConstructors()) { continue; }
        H::DatatypeDecl decl;
        decl.name = sort_name;
        decl.coinductive = s->coinductive;
        // `(par (X) ...)`. Carried across because a selector's sort mentions the
        // parameters and the lowering has to write the same form back; without
        // them a parametric declaration came out as an arity-0 one.
        decl.params = parser_->datatypeParams(sort_name);
        for (const Sort::DtConstructor& c : s->getDtConstructors()) {
            H::DtConstructor ctor;
            ctor.name = c.name;
            for (const Sort::DtSelector& sel : c.selectors) {
                H::DtSelector out_sel;
                out_sel.name = sel.name;
                if (!liftSort(sel.sort, out_sel.sort, diagnostics)) { return false; }
                ctor.selectors.push_back(std::move(out_sel));
            }
            decl.constructors.push_back(std::move(ctor));
        }
        for (const H::DtConstructor& c : decl.constructors) {
            datatype_members_.insert(c.name);
            datatype_members_.insert("is-" + c.name);
            for (const H::DtSelector& sel : c.selectors) {
                datatype_members_.insert(sel.name);
            }
        }
        out.datatypes.push_back(std::move(decl));
    }
    for (const auto& v : parser_->getDeclaredVariables()) {
        H::VarDecl d;
        d.name = v->getName();
        if (!liftSort(v->getSort(), d.sort, diagnostics)) { return false; }
        out.decls.push_back(std::move(d));
    }
    // Function declarations, without which an application in a constraint names
    // a symbol the model never introduces. That is not a cosmetic omission:
    // Uir::Hir::typeCheck rejects the model, and if it did not, HirToParser
    // would emit a script applying an undeclared symbol. CHC's whole subject
    // matter is uninterpreted predicates, so this is its load-bearing case
    // rather than a corner of it.
    for (const auto& f : parser_->getFunctions()) {
        // ...except the ones a datatype declaration created. `(declare-datatypes
        // ...)` registers a declare-fun for every constructor, selector and
        // tester, and those are already carried by the DatatypeDecl above. A
        // second declaration beside it makes the emitted script refuse itself
        // as a redeclaration.
        if (isDatatypeMember(f->getName())) { continue; }
        H::FunDecl d;
        d.name = f->getName();
        if (!liftSort(f->getSort(), d.result, diagnostics)) { return false; }
        const std::vector<std::shared_ptr<DAGNode>> params = f->getFuncParams();
        for (const auto& p : params) {
            H::Sort ps;
            if (!liftSort(p->getSort(), ps, diagnostics)) { return false; }
            d.params.push_back(ps);
        }
        out.funs.push_back(d);

        // A `define-fun` carries a BODY, and dropping it would leave the symbol
        // uninterpreted -- a strictly weaker model that type-checks, answers a
        // different question, and reports success. So the definition crosses as
        // an axiom: `forall x. f(x) = body`.
        //
        // An axiom rather than an inlining, for the reason Boogie's frontend
        // gives: it keeps the one symbol and one defining equation the source
        // wrote, and the emitted script reads like its input. SMT-LIB's
        // define-fun is non-recursive by definition, so both are exact here;
        // the axiom form is also what survives if define-fun-rec is ever added.
        // define-fun-rec too, and the axiom form is the reason it can be:
        // SMT-LIB's define-fun-rec MEANS the equation `forall x. f(x) = body`,
        // so emitting it is the definition rather than an approximation of one.
        // An inliner could not have done this at all.
        if (!f->isFuncDef() && !f->isFuncRec()) { continue; }
        std::shared_ptr<DAGNode> body = f->getFuncBody();
        if (!body) { continue; }

        // The parameters are bound variables of the axiom, so they are pushed
        // into the same scope machinery a quantifier uses -- an IDENT here
        // would make them free variables of the model.
        std::vector<H::Binder> binders;
        std::vector<std::pair<std::string, std::optional<Binding>>> saved;
        for (std::size_t i = 0; i < params.size(); ++i) {
            H::Binder b;
            // Parameters keep the existing unconditional alpha-renaming
            // policy, using the same collision checks as quantifier binders.
            const std::string source_name = boundSymbolKey(params[i]->getName());
            b.name = freshBoundName(params[i]->getName(), true);
            active_bound_names_.insert(boundSymbolKey(b.name));
            b.sort = d.params[i];
            binders.push_back(b);
            const auto prev = bound_.find(source_name);
            saved.emplace_back(source_name,
                               prev == bound_.end() ? std::nullopt
                                                    : std::optional<Binding>(prev->second));
            bound_[source_name] = Binding{b.name, b.sort};
        }
        ++scope_id_;
        H::ExprPtr hir_body = liftNumericChild(body, &d.result, diagnostics);
        ++scope_id_;
        for (const auto& binder : binders) {
            active_bound_names_.erase(boundSymbolKey(binder.name));
        }
        for (auto it = saved.rbegin(); it != saved.rend(); ++it) {
            if (it->second) { bound_[it->first] = *it->second; }
            else            { bound_.erase(it->first); }
        }
        if (!hir_body) { return false; }

        if (retain_nonrecursive_definitions && f->isFuncDef() && !f->isFuncRec()) {
            H::FunDecl& lifted = out.funs.back();
            lifted.body = std::move(hir_body);
            lifted.binders = std::move(binders);
            continue;
        }

        // A define-funs-rec group must cross into HIR as definitions in one
        // explicit recursion component. Turning it into separate universally
        // quantified equations loses the group binding scope used by the
        // Parser dumper and the HIR lowerer. Standalone define-fun-rec remains
        // on the legacy equation path unless a complete group was recorded.
        if (f->isFuncRec()) {
            const auto* recursive_group =
                parser_->getSymbolManager()->getRecFunGroup(f->getName());
            if (recursive_group && !recursive_group->empty()) {
                H::FunDecl& lifted = out.funs.back();
                lifted.body = std::move(hir_body);
                lifted.binders = std::move(binders);
                lifted.recursive_group = "__parser_rec_group__" + recursive_group->front();
                continue;
            }
        }

        std::vector<H::ExprPtr> args;
        args.reserve(binders.size());
        for (const H::Binder& b : binders) { args.push_back(H::mkBoundVar(b.name, b.sort)); }
        H::ExprPtr call = H::mkApply(d.name, d.result, args);
        H::ExprPtr eq = H::mkOp(H::Op::EQ, {call, hir_body});
        H::Constraint c;
        c.formula = binders.empty() ? eq : H::mkForall(binders, eq);
        out.constraints.push_back(std::move(c));
    }
    for (const auto& a : parser_->getAssertions()) {
        H::ExprPtr f = liftExpr(a, diagnostics);
        if (!f) { return false; }
        H::Constraint c;
        c.formula = std::move(f);
        out.constraints.push_back(std::move(c));
    }
    return true;
}

} // namespace SOMTParser::Lower
