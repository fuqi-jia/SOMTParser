/* -*- Source -*-
 * HIR type checking. See the header for why this lives here and not in each
 * frontend.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/hir/typecheck.h"
#include "somtparser/hir/packed_linear_io.h"
#include "somtparser/hir/packed_scalar_io.h"

#include "somtparser/core/asserting.h"
#include "somtparser/core/root_expression_cache.h"
#include "somtparser/hir/soft_objectives.h"

#include <algorithm>
#include <cmath>
#include <regex>
#include <functional>
#include <limits>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Uir::Hir {

namespace {

bool isNumeric(SortKind k) {
    return k == SortKind::INT || k == SortKind::REAL;
}

/** The globals this build knows, and what each requires of its arguments.
 *  A global not in this table is refused by name rather than passed through:
 *  decompose-globals would then meet something it cannot eliminate, and the
 *  pass manager would blame the profile for what is really thin coverage. */
struct GlobalRule {
    const char* name;
    /** The INDEXED shape's exact arity; 0 when the global has no indexed
     *  shape. Dispatched on the first argument's sort, not on the count. */
    std::size_t arity;
    /** The LIST shape's minimum arity; 0 when the global has no list shape. */
    std::size_t list_min;
    const char* shape;      // for the diagnostic
};

const GlobalRule* globalRule(const std::string& name) {
    static const GlobalRule kRules[] = {
        // Two shapes, and the first argument's SORT says which:
        //
        //   alldifferent(array, lo, hi)  the elements at indices lo..hi-1 are
        //       pairwise distinct. The bounds are arguments rather than part of
        //       the array's sort, because an SMT-LIB array is total (see hir.h).
        //
        //   alldifferent(t1, t2, ...)    these terms are pairwise distinct.
        //       Needed because `alldifferent([x, y, z])` and
        //       `alldifferent(i in S)(f(i))` are ordinary MiniZinc and neither
        //       has an array to point at -- the second one's terms are computed.
        //
        // Dispatching on the sort rather than on the count is what keeps the
        // two apart: a three-element list form would otherwise be read as an
        // indexed one and silently constrain the wrong thing.
        {"alldifferent", 3, 2, "alldifferent(array, lo, hi) or alldifferent(t1, t2, ...)"},
        {"alldifferent_except_0", 3, 1,
         "alldifferent_except_0(array, lo, hi) or alldifferent_except_0(t1, ..., tn)"},
        {"connected", 0, 2,
         "connected(N, E, from[0..E), to[0..E), nodes[0..N), edges[0..E))"},
        {"dconnected", 0, 2,
         "dconnected(N, E, from[0..E), to[0..E), nodes[0..N), edges[0..E))"},
        // count carries the same two shapes for the same reason, and the last
        // two arguments are always the sought VALUE and the number of times it
        // occurs -- `count(x, y, c)` in MiniZinc's own signature order:
        //
        //   count(array, lo, hi, y, c)   c is how many of the elements at
        //       indices lo..hi-1 equal y.
        //
        //   count(t1, ..., tn, y, c)     c is how many of the terms equal y.
        //       The list form is the one a comprehension reaches:
        //       `count([a[r,c] | c in col], 0, k)` has no array to point at.
        //
        // The list minimum is 3 -- one term, the value, the count. Counting
        // over NO terms is a legal `c = 0`, and it is folded by the frontend
        // rather than admitted here, the same way alldifferent folds fewer
        // than two terms to `true`: a one-or-zero-term list shape would be a
        // shape with nothing to say, and the checker could no longer tell a
        // degenerate global from a malformed one.
        {"count", 5, 3, "count(array, lo, hi, y, c) or count(t1, ..., tn, y, c)"},
        {"count_value", 0, 2, "count_value(length, sought, terms...)"},
        // Explicit successors at consecutive indices starting at `start`.
        // A list with just start is the empty circuit; self loops are excluded.
        {"circuit", 0, 1, "circuit(start, successor1, ..., successorN)"},
        {"table", 0, 2, "table(columns, rows, tuple..., row-major cells...)"},
        {"inverse", 0, 3, "inverse(left_start, right_start, left_size, left..., right...)"},
        {"cumulative", 0, 1, "cumulative(capacity, start, duration, demand, ...)"},
        {"diffn", 0, 1, "diffn(dimensions, box-major position/size pairs...)"},
        {"diffn_nonstrict", 0, 1, "diffn_nonstrict(dimensions, box-major position/size pairs...)"},
    };
    for (const auto& r : kRules) {
        if (name == r.name) { return &r; }
    }
    return nullptr;
}

const char* opName(Op op) {
    switch (op) {
    case Op::AND: return "and";
    case Op::OR:  return "or";
    case Op::NOT: return "not";
    case Op::XOR: return "xor";
    case Op::ITE: return "ite";
    case Op::SELECT: return "select";
    case Op::ARRAY_MAP_AND: return "array.map.and";
    case Op::ARRAY_MAP_OR: return "array.map.or";
    case Op::ARRAY_MAP_NOT: return "array.map.not";
    case Op::STORE:  return "store";
    case Op::EQ:  return "=";
    case Op::LE:  return "<=";
    case Op::LT:  return "<";
    case Op::GE:  return ">=";
    case Op::GT:  return ">";
    case Op::ADD: return "+";
    case Op::SUB: return "-";
    case Op::MUL: return "*";
    case Op::IMPLIES: return "=>";
    case Op::DISTINCT: return "distinct";
    case Op::NEG: return "-";
    case Op::ABS: return "abs";
    // Euclidean is SMT-LIB's own div/mod, so it keeps the SMT-LIB spelling.
    // The other two must NOT: a diagnostic that called truncating division
    // "div" would name an operator whose emitted form is a correction term
    // around SMT-LIB's div, and a reader comparing the message with the script
    // would be looking for the wrong thing.
    case Op::DIV_EUCLID: return "div";
    case Op::MOD_EUCLID: return "mod";
    case Op::DIV_TRUNC:  return "div_trunc";
    case Op::MOD_TRUNC:  return "mod_trunc";
    case Op::DIV_FLOOR:  return "div_floor";
    case Op::MOD_FLOOR:  return "mod_floor";
    case Op::DIV_REAL:   return "/";
    // The SMT-LIB names, so a diagnostic about a translated BTOR2 line names
    // the operator the reader will find in the emitted script.
    case Op::BV_NOT:  return "bvnot";
    case Op::BV_NEG:  return "bvneg";
    case Op::BV_AND:  return "bvand";
    case Op::BV_OR:   return "bvor";
    case Op::BV_XOR:  return "bvxor";
    case Op::BV_NAND: return "bvnand";
    case Op::BV_NOR:  return "bvnor";
    case Op::BV_XNOR: return "bvxnor";
    case Op::BV_ADD:  return "bvadd";
    case Op::BV_SUB:  return "bvsub";
    case Op::BV_MUL:  return "bvmul";
    case Op::BV_UDIV: return "bvudiv";
    case Op::BV_UREM: return "bvurem";
    case Op::BV_SDIV: return "bvsdiv";
    case Op::BV_SREM: return "bvsrem";
    case Op::BV_SMOD: return "bvsmod";
    case Op::BV_SHL:  return "bvshl";
    case Op::BV_LSHR: return "bvlshr";
    case Op::BV_ASHR: return "bvashr";
    case Op::BV_ULT:  return "bvult";
    case Op::BV_ULE:  return "bvule";
    case Op::BV_UGT:  return "bvugt";
    case Op::BV_UGE:  return "bvuge";
    case Op::BV_SLT:  return "bvslt";
    case Op::BV_SLE:  return "bvsle";
    case Op::BV_SGT:  return "bvsgt";
    case Op::BV_SGE:  return "bvsge";
    case Op::BV_CONCAT:      return "concat";
    case Op::BV_EXTRACT:     return "extract";
    case Op::BV_ZERO_EXTEND: return "zero_extend";
    case Op::BV_SIGN_EXTEND: return "sign_extend";
    case Op::BV_ROTATE_LEFT: return "rotate_left";
    case Op::BV_ROTATE_RIGHT: return "rotate_right";
    case Op::BV_REPEAT: return "repeat";
    case Op::BV_COMP: return "bvcomp";
    case Op::FP_ADD: return "fp.add";
    case Op::FP_SUB: return "fp.sub";
    case Op::FP_MUL: return "fp.mul";
    case Op::FP_DIV: return "fp.div";
    case Op::FP_FMA: return "fp.fma";
    case Op::FP_SQRT: return "fp.sqrt";
    case Op::FP_ROUND_TO_INTEGRAL: return "fp.roundToIntegral";
    case Op::FP_ABS: return "fp.abs";
    case Op::FP_NEG: return "fp.neg";
    case Op::FP_REM: return "fp.rem";
    case Op::FP_MIN: return "fp.min";
    case Op::FP_MAX: return "fp.max";
    case Op::FP_LEQ: return "fp.leq";
    case Op::FP_LT:  return "fp.lt";
    case Op::FP_GEQ: return "fp.geq";
    case Op::FP_GT:  return "fp.gt";
    case Op::FP_EQ:  return "fp.eq";
    case Op::FP_IS_NORMAL:    return "fp.isNormal";
    case Op::FP_IS_SUBNORMAL: return "fp.isSubnormal";
    case Op::FP_IS_ZERO:      return "fp.isZero";
    case Op::FP_IS_INFINITE:  return "fp.isInfinite";
    case Op::FP_IS_NAN:       return "fp.isNaN";
    case Op::FP_IS_NEGATIVE:  return "fp.isNegative";
    case Op::FP_IS_POSITIVE:  return "fp.isPositive";
    case Op::STR_CONCAT:      return "str.++";
    case Op::STR_LEN:         return "str.len";
    case Op::STR_AT:          return "str.at";
    case Op::STR_SUBSTR:      return "str.substr";
    case Op::STR_INDEXOF:     return "str.indexof";
    case Op::STR_REPLACE:     return "str.replace";
    case Op::STR_REPLACE_ALL: return "str.replace_all";
    case Op::STR_CONTAINS:    return "str.contains";
    case Op::STR_PREFIXOF:    return "str.prefixof";
    case Op::STR_SUFFIXOF:    return "str.suffixof";
    case Op::STR_LT:          return "str.<";
    case Op::STR_LE:          return "str.<=";
    case Op::STR_TO_INT:      return "str.to_int";
    case Op::STR_FROM_INT:    return "str.from_int";
    case Op::STR_TO_CODE: return "str.to_code";
    case Op::STR_IS_DIGIT: return "str.is_digit";
    case Op::STR_INDEXOF_RE: return "str.indexof_re";
    case Op::STR_REPLACE_RE: return "str.replace_re";
    case Op::STR_REPLACE_RE_ALL: return "str.replace_re_all";
    case Op::CONST_ARRAY: return "const array";
    case Op::STR_FROM_CODE: return "str.from_code";
    case Op::STR_TO_RE: return "str.to_re";
    case Op::STR_IN_RE: return "str.in_re";
    case Op::RE_CONCAT: return "re.++";
    case Op::RE_UNION: return "re.union";
    case Op::RE_INTER: return "re.inter";
    case Op::RE_DIFF: return "re.diff";
    case Op::RE_STAR: return "re.*";
    case Op::RE_PLUS: return "re.+";
    case Op::RE_OPT: return "re.opt";
    case Op::RE_COMPLEMENT: return "re.comp";
    case Op::RE_RANGE: return "re.range";
    case Op::RE_LOOP: return "re.loop";
    case Op::TO_INT: return "to_int";
    case Op::TO_REAL: return "to_real";
    case Op::IS_INT: return "is_int";
    case Op::IS_DIVISIBLE: return "divisible";
    case Op::BV_TO_NAT: return "bv2nat";
    case Op::BV_TO_INT: return "bv2int";
    case Op::INT_TO_BV: return "int2bv";
    case Op::FP_TO_REAL: return "fp.to_real";
    case Op::FP_TO_IEEE_BV: return "fp.to_ieee_bv";
    case Op::FP_TO_SBV: return "fp.to_sbv";
    case Op::FP_TO_UBV: return "fp.to_ubv";
    case Op::TO_FP: return "to_fp";
    case Op::TO_FP_UNSIGNED: return "to_fp_unsigned";
    case Op::IEEE_BV_TO_FP: return "to_fp (bit-pattern)";
    case Op::SET_SINGLETON: return "set.singleton";
    case Op::SET_UNION: return "set.union";
    case Op::SET_INTER: return "set.inter";
    case Op::SET_MINUS: return "set.minus";
    case Op::SET_MEMBER: return "set.member";
    case Op::SET_SUBSET: return "set.subset";
    case Op::SET_CARD: return "set.card";
    case Op::SET_INSERT: return "set.insert";
    case Op::SET_COMPLEMENT: return "set.complement";
    case Op::TUPLE: return "tuple";
    case Op::TUPLE_SELECT: return "tuple.select";
    case Op::TUPLE_UPDATE: return "tuple.update";
    case Op::TUPLE_PROJECT: return "tuple.project";
    }
    // Unhandled here means a new Op was added without teaching this checker
    // about it, and every model using it would then pass unchecked. Naming it
    // "?" and carrying on is exactly the silence this file exists to remove.
    return nullptr;
}

/** What each operator demands of its arguments and yields as a result. */
struct OpRule {
    std::size_t min_args;
    std::size_t max_args;      // 0 means unbounded
    enum class Args {
        BOOL,
        NUMERIC,
        SAME_ANY,
        /** Every argument a bit-vector of the *same* width. SMT-LIB requires it
         *  even for the shifts, where a reader might expect the distance to be
         *  narrower -- (bvshl x y) has both operands at x's width. */
        BITVEC_SAME,
        /** Every argument a bit-vector, widths free. Only concat. */
        BITVEC_ANY,
        /** Positional: each argument's SortKind is given by signatureFor().
         *  Used by the floating-point and string families, whose argument
         *  shapes are irregular -- (rm, Float, Float), (String, Int, Int),
         *  (String, String, Int) -- and cannot be described by "all the same". */
        SIGNATURE,
    } args;
    enum class Result {
        BOOL,
        /** The widened argument sort: Real dominates Int. Arithmetic only. */
        WIDENED,
        /** The first argument's sort, width included. */
        ARG0,
        /** The sum of the argument widths. */
        CONCAT_WIDTH,
        /** Computed from Expr::indices; checkIndexed does it. */
        INDEXED,
        /** The SECOND argument's sort. The floating-point arithmetic operators
         *  take a RoundingMode first, so ARG0 would make every fp.add a
         *  RoundingMode. */
        ARG1,
        INT_RESULT,
        STRING_RESULT,
        REAL_RESULT,
        REGLAN_RESULT,
        /** A one-bit vector, whatever the arguments' width. Only bvcomp, and
         *  spelled out rather than folded into BOOL because the difference is
         *  the point: `#b1` is a value that concatenates and shifts, `true` is
         *  not. */
        BITVEC_ONE,
    } result;
    /** How many entries Expr::indices must hold. */
    std::size_t index_count = 0;
};

bool ruleFor(Op op, OpRule& out) {
    using A = OpRule::Args;
    using R = OpRule::Result;
    switch (op) {
    case Op::AND:
    case Op::OR:  out = {1, 0, A::BOOL,     R::BOOL};    return true;
    case Op::NOT: out = {1, 1, A::BOOL,     R::BOOL};    return true;
    case Op::XOR: out = {2, 0, A::BOOL,     R::BOOL};    return true;
    // Binary, because SMT-LIB's => is right-associative: an n-ary chain has a
    // different meaning from a flat one, so it is built as nested applications
    // rather than accepted here and flattened.
    case Op::IMPLIES: out = {2, 2, A::BOOL, R::BOOL};    return true;
    // n-ary and PAIRWISE. (distinct a b c) says all three differ; a chain of
    // != would permit a = c.
    case Op::DISTINCT: out = {2, 0, A::SAME_ANY, R::BOOL}; return true;
    // ite's rule is structural -- a Bool condition and two branches of one
    // sort, any sort -- so checkOp handles it directly, like SELECT.
    case Op::ITE: return false;
    // = is the one comparison that also relates Bools, so its arguments only
    // have to agree with each other. The ordered comparisons do not: (< b true)
    // has no meaning to give.
    // SMT equality is chainable: all operands have one common value.
    case Op::EQ:  out = {2, 0, A::SAME_ANY, R::BOOL};    return true;
    case Op::LE:
    case Op::LT:
    case Op::GE:
    case Op::GT:  out = {2, 0, A::NUMERIC,  R::BOOL};    return true;
    case Op::SUB: out = {2, 2, A::NUMERIC,  R::WIDENED}; return true;
    case Op::NEG:
    case Op::ABS: out = {1, 1, A::NUMERIC,  R::ARG0};    return true;
    case Op::ADD:
    case Op::MUL: out = {1, 0, A::NUMERIC,  R::WIDENED}; return true;
    // Integer division and remainder: strictly two Ints in, one Int out.
    // NUMERIC would admit a Real operand and WIDENED would then make the
    // result Real, which is a different operator -- `(div 7 2.0)` has no
    // meaning to give, and silently answering 3.5 for it is worse than
    // refusing. Written as a positional signature so the arity error and the
    // sort error stay separate diagnostics.
    case Op::DIV_EUCLID: case Op::DIV_TRUNC: case Op::DIV_FLOOR:
    case Op::MOD_EUCLID: case Op::MOD_TRUNC: case Op::MOD_FLOOR:
                  out = {2, 2, A::SIGNATURE, R::INT_RESULT}; return true;
    // Real division takes Int operands happily; what it must not do is yield
    // an Int for them. `(/ 1 2)` is one half.
    case Op::DIV_REAL:
                  out = {2, 2, A::NUMERIC,  R::REAL_RESULT}; return true;
    // One argument and one index. NUMERIC would admit a Real, and
    // divisibility of a Real is not a weaker question but a meaningless one.
    case Op::IS_DIVISIBLE:
                  out = {1, 1, A::SIGNATURE, R::BOOL, 1};      return true;

    // ---- Bit-vectors ----------------------------------------------------
    case Op::BV_NOT:
    case Op::BV_NEG:  out = {1, 1, A::BITVEC_SAME, R::ARG0}; return true;
    // n-ary where SMT-LIB is n-ary, binary where it is binary: bvand and bvadd
    // are left-associative and take any number, the divisions and shifts do
    // not, and accepting three arguments for bvudiv would build a term the
    // engine cannot lower.
    case Op::BV_AND:  case Op::BV_OR:   case Op::BV_XOR:
    case Op::BV_ADD:  case Op::BV_MUL:
                      out = {1, 0, A::BITVEC_SAME, R::ARG0}; return true;
    case Op::BV_NAND: case Op::BV_NOR:  case Op::BV_XNOR:
    case Op::BV_SUB:
    case Op::BV_UDIV: case Op::BV_UREM:
    case Op::BV_SDIV: case Op::BV_SREM: case Op::BV_SMOD:
    case Op::BV_SHL:  case Op::BV_LSHR: case Op::BV_ASHR:
                      out = {2, 2, A::BITVEC_SAME, R::ARG0}; return true;
    case Op::BV_ULT: case Op::BV_ULE: case Op::BV_UGT: case Op::BV_UGE:
    case Op::BV_SLT: case Op::BV_SLE: case Op::BV_SGT: case Op::BV_SGE:
                      out = {2, 2, A::BITVEC_SAME, R::BOOL}; return true;
    case Op::BV_CONCAT:
                      out = {2, 0, A::BITVEC_ANY, R::CONCAT_WIDTH}; return true;
    case Op::BV_EXTRACT:
                      out = {1, 1, A::BITVEC_ANY, R::INDEXED, 2}; return true;
    case Op::BV_ZERO_EXTEND:
    case Op::BV_SIGN_EXTEND:
                      out = {1, 1, A::BITVEC_ANY, R::INDEXED, 1}; return true;
    // Rotations and repeat are indexed too, and the three compute three
    // different widths from the same shape -- preserved, preserved, multiplied
    // -- which is why the INDEXED branch names each rather than sharing the
    // extensions' `w + n`.
    case Op::BV_ROTATE_LEFT:
    case Op::BV_ROTATE_RIGHT:
    case Op::BV_REPEAT:
                      out = {1, 1, A::BITVEC_ANY, R::INDEXED, 1}; return true;
    // Both operands at one width, like every other bit-vector comparison --
    // and unlike them, the result is a bit, not a Bool.
    case Op::BV_COMP: out = {2, 2, A::BITVEC_SAME, R::BITVEC_ONE}; return true;

    // ---- Floating point --------------------------------------------------
    // Argument shapes are positional, so they live in signatureFor(); the arity
    // is repeated here because a wrong count must be reported as a count and not
    // as a sort mismatch on a missing argument.
    case Op::FP_ADD: case Op::FP_SUB: case Op::FP_MUL: case Op::FP_DIV:
                     out = {3, 3, A::SIGNATURE, R::ARG1}; return true;
    case Op::FP_FMA: out = {4, 4, A::SIGNATURE, R::ARG1}; return true;
    case Op::FP_SQRT: case Op::FP_ROUND_TO_INTEGRAL:
                     out = {2, 2, A::SIGNATURE, R::ARG1}; return true;
    case Op::FP_ABS: case Op::FP_NEG:
                     out = {1, 1, A::SIGNATURE, R::ARG0}; return true;
    case Op::FP_REM: case Op::FP_MIN: case Op::FP_MAX:
                     out = {2, 2, A::SIGNATURE, R::ARG0}; return true;
    case Op::FP_LEQ: case Op::FP_LT: case Op::FP_GEQ: case Op::FP_GT:
    case Op::FP_EQ:  out = {2, 2, A::SIGNATURE, R::BOOL}; return true;
    case Op::FP_IS_NORMAL: case Op::FP_IS_SUBNORMAL: case Op::FP_IS_ZERO:
    case Op::FP_IS_INFINITE: case Op::FP_IS_NAN: case Op::FP_IS_NEGATIVE:
    case Op::FP_IS_POSITIVE:
                     out = {1, 1, A::SIGNATURE, R::BOOL}; return true;

    // ---- Strings ---------------------------------------------------------
    case Op::STR_CONCAT:  out = {1, 0, A::SIGNATURE, R::STRING_RESULT}; return true;
    case Op::STR_LEN:     out = {1, 1, A::SIGNATURE, R::INT_RESULT};    return true;
    case Op::STR_TO_INT:  out = {1, 1, A::SIGNATURE, R::INT_RESULT};    return true;
    case Op::STR_FROM_INT:out = {1, 1, A::SIGNATURE, R::STRING_RESULT}; return true;
    case Op::STR_AT:      out = {2, 2, A::SIGNATURE, R::STRING_RESULT}; return true;
    case Op::STR_SUBSTR:  out = {3, 3, A::SIGNATURE, R::STRING_RESULT}; return true;
    case Op::STR_INDEXOF: out = {3, 3, A::SIGNATURE, R::INT_RESULT};    return true;
    case Op::STR_REPLACE: case Op::STR_REPLACE_ALL:
                          out = {3, 3, A::SIGNATURE, R::STRING_RESULT}; return true;
    case Op::STR_CONTAINS: case Op::STR_PREFIXOF: case Op::STR_SUFFIXOF:
    case Op::STR_LT: case Op::STR_LE:
                          out = {2, 2, A::SIGNATURE, R::BOOL};          return true;
    case Op::STR_IS_DIGIT:out = {1, 1, A::SIGNATURE, R::BOOL};          return true;
    case Op::STR_INDEXOF_RE:
                          out = {3, 3, A::SIGNATURE, R::INT_RESULT};    return true;
    case Op::STR_REPLACE_RE: case Op::STR_REPLACE_RE_ALL:
                          out = {3, 3, A::SIGNATURE, R::STRING_RESULT}; return true;
    // The array sort comes from the expression, not from the argument, so
    // checkOp handles it directly -- like SELECT and STORE.
    case Op::CONST_ARRAY:  return false;

    // ---- Regular expressions ---------------------------------------------
    case Op::STR_TO_CODE:   out = {1, 1, A::SIGNATURE, R::INT_RESULT};    return true;
    case Op::STR_FROM_CODE: out = {1, 1, A::SIGNATURE, R::STRING_RESULT}; return true;
    case Op::STR_TO_RE:     out = {1, 1, A::SIGNATURE, R::REGLAN_RESULT}; return true;
    case Op::STR_IN_RE:     out = {2, 2, A::SIGNATURE, R::BOOL};          return true;
    case Op::RE_CONCAT: case Op::RE_UNION: case Op::RE_INTER: case Op::RE_DIFF:
                            out = {1, 0, A::SIGNATURE, R::REGLAN_RESULT}; return true;
    case Op::RE_STAR: case Op::RE_PLUS: case Op::RE_OPT: case Op::RE_COMPLEMENT:
                            out = {1, 1, A::SIGNATURE, R::REGLAN_RESULT}; return true;
    case Op::RE_RANGE:      out = {2, 2, A::SIGNATURE, R::REGLAN_RESULT}; return true;
    case Op::RE_LOOP:       out = {1, 1, A::SIGNATURE, R::REGLAN_RESULT, 2}; return true;

    // ---- Conversions ------------------------------------------------------
    case Op::TO_INT:        out = {1, 1, A::SIGNATURE, R::INT_RESULT};    return true;
    case Op::TO_REAL:       out = {1, 1, A::SIGNATURE, R::REAL_RESULT};   return true;
    case Op::IS_INT:        out = {1, 1, A::SIGNATURE, R::BOOL};          return true;
    case Op::BV_TO_NAT: case Op::BV_TO_INT:
                            out = {1, 1, A::SIGNATURE, R::INT_RESULT};    return true;
    case Op::INT_TO_BV:     out = {1, 1, A::SIGNATURE, R::INDEXED, 1};    return true;
    case Op::FP_TO_REAL:    out = {1, 1, A::SIGNATURE, R::REAL_RESULT};   return true;
    case Op::FP_TO_IEEE_BV: out = {1, 1, A::SIGNATURE, R::INDEXED};       return true;
    case Op::FP_TO_SBV: case Op::FP_TO_UBV:
                            out = {2, 2, A::SIGNATURE, R::INDEXED, 1};    return true;
    case Op::TO_FP: case Op::TO_FP_UNSIGNED:
                            out = {2, 2, A::SIGNATURE, R::INDEXED, 2};    return true;
    case Op::IEEE_BV_TO_FP: out = {1, 1, A::SIGNATURE, R::INDEXED, 2};    return true;

    // Sets: like SELECT and STORE, the rules relate a container sort to its
    // element sort rather than demanding one uniform kind, so checkOp handles
    // them directly.
    case Op::SET_SINGLETON: case Op::SET_UNION: case Op::SET_INTER:
    case Op::SET_MINUS: case Op::SET_MEMBER: case Op::SET_SUBSET:
    case Op::SET_CARD: case Op::SET_INSERT: case Op::SET_COMPLEMENT:
        return false;

    // Tuples: no uniform rule exists even in principle -- a tuple's arguments
    // are a heterogeneous list and three of the four operators take their
    // shape from an INDEX rather than from a sort. checkTupleOp handles them.
    case Op::TUPLE: case Op::TUPLE_SELECT: case Op::TUPLE_UPDATE:
    case Op::TUPLE_PROJECT:
        return false;

    // SELECT's argument rule is structural rather than sort-uniform -- an array
    // and an index of that array's index sort -- so checkOp handles it directly
    // and ruleFor does not describe it.
    case Op::SELECT:
    case Op::ARRAY_MAP_AND: case Op::ARRAY_MAP_OR: case Op::ARRAY_MAP_NOT:
    case Op::STORE: return false;
    }
    return false;
}

/**
 * The expected SortKind of each argument position.
 *
 * @param variadic true when the last entry repeats for every further argument
 *                 (only str.++).
 * Returns false for an operator that does not use OpRule::Args::SIGNATURE.
 */
bool signatureFor(Op op, std::vector<SortKind>& sig, bool& variadic) {
    const SortKind RM = SortKind::ROUNDING_MODE;
    const SortKind F  = SortKind::FLOAT;
    const SortKind S  = SortKind::STRING;
    const SortKind I  = SortKind::INT;
    const SortKind R  = SortKind::REGLAN;
    variadic = false;
    switch (op) {
    case Op::DIV_EUCLID: case Op::DIV_TRUNC: case Op::DIV_FLOOR:
    case Op::MOD_EUCLID: case Op::MOD_TRUNC: case Op::MOD_FLOOR:
        sig = {I, I}; return true;
    case Op::FP_ADD: case Op::FP_SUB: case Op::FP_MUL: case Op::FP_DIV:
        sig = {RM, F, F}; return true;
    case Op::FP_FMA:  sig = {RM, F, F, F}; return true;
    case Op::FP_SQRT: case Op::FP_ROUND_TO_INTEGRAL:
        sig = {RM, F}; return true;
    case Op::FP_ABS: case Op::FP_NEG:
        sig = {F}; return true;
    case Op::FP_REM: case Op::FP_MIN: case Op::FP_MAX:
    case Op::FP_LEQ: case Op::FP_LT: case Op::FP_GEQ: case Op::FP_GT:
    case Op::FP_EQ:
        sig = {F, F}; return true;
    case Op::FP_IS_NORMAL: case Op::FP_IS_SUBNORMAL: case Op::FP_IS_ZERO:
    case Op::FP_IS_INFINITE: case Op::FP_IS_NAN: case Op::FP_IS_NEGATIVE:
    case Op::FP_IS_POSITIVE:
        sig = {F}; return true;
    case Op::STR_CONCAT:  sig = {S};       variadic = true; return true;
    case Op::STR_LEN: case Op::STR_TO_INT: sig = {S};       return true;
    case Op::STR_FROM_INT:sig = {I};       return true;
    case Op::STR_AT:      sig = {S, I};    return true;
    case Op::STR_SUBSTR:  sig = {S, I, I}; return true;
    case Op::STR_INDEXOF: sig = {S, S, I}; return true;
    case Op::STR_REPLACE: case Op::STR_REPLACE_ALL:
                          sig = {S, S, S}; return true;
    case Op::STR_CONTAINS: case Op::STR_PREFIXOF: case Op::STR_SUFFIXOF:
    case Op::STR_LT: case Op::STR_LE:
                          sig = {S, S};    return true;
    case Op::STR_TO_CODE:   sig = {S};    return true;
    case Op::STR_IS_DIGIT:  sig = {S};    return true;
    case Op::STR_INDEXOF_RE: sig = {S, R, I}; return true;
    case Op::STR_REPLACE_RE: case Op::STR_REPLACE_RE_ALL:
                            sig = {S, R, S}; return true;
    case Op::STR_FROM_CODE: sig = {I};    return true;
    case Op::STR_TO_RE:     sig = {S};    return true;
    case Op::STR_IN_RE:     sig = {S, R};  return true;
    case Op::RE_CONCAT: case Op::RE_UNION: case Op::RE_INTER: case Op::RE_DIFF:
        sig = {R}; variadic = true; return true;
    case Op::RE_STAR: case Op::RE_PLUS: case Op::RE_OPT: case Op::RE_COMPLEMENT:
    case Op::RE_LOOP:
        sig = {R}; return true;
    case Op::RE_RANGE:      sig = {S, S}; return true;
    case Op::TO_INT:        sig = {SortKind::REAL}; return true;
    case Op::IS_INT:        sig = {SortKind::REAL}; return true;
    case Op::IS_DIVISIBLE:  sig = {I};    return true;
    case Op::TO_REAL:       sig = {I};    return true;
    case Op::BV_TO_NAT: case Op::BV_TO_INT: case Op::FP_TO_IEEE_BV:
        sig = {op == Op::FP_TO_IEEE_BV ? F : SortKind::BITVEC}; return true;
    case Op::INT_TO_BV:     sig = {I};    return true;
    case Op::FP_TO_REAL:    sig = {F};    return true;
    case Op::FP_TO_SBV: case Op::FP_TO_UBV:
        sig = {RM, F}; return true;
    case Op::TO_FP: case Op::TO_FP_UNSIGNED:
        // The source may be Real, Float or BitVec, so the second position is
        // checked by checkOp rather than by a fixed kind here.
        sig = {RM, SortKind::BOOL}; return true;
    case Op::IEEE_BV_TO_FP:
        sig = {SortKind::BITVEC}; return true;
    default:
        return false;
    }
}

/** The sort mkOp() derives for an arithmetic result: Real dominates Int.
 *  Only ever asked about operators whose arguments were already confirmed
 *  numeric, so Bool cannot reach it. */
SortKind widened(const std::vector<ExprPtr>& args) {
    for (const auto& a : args) {
        if (a->sort.kind == SortKind::REAL) { return SortKind::REAL; }
    }
    return SortKind::INT;
}

/** Where to point the reader when the expression itself carries no location. */
const SourceLoc& locOf(const ExprPtr& e, const SourceLoc& fallback) {
    return e->loc.file.empty() ? fallback : e->loc;
}

class Checker {
public:
    Checker(const ConstraintModel& model, Diagnostics& diagnostics)
        : model_(model), diags_(diagnostics), scalar_ranges_(model) {}

    bool run() {
        checkUninterpretedSorts();
        checkDatatypes();
        checkFuns();
        checkDecls();
        checkPackedBoolClauses();
        if (!validatePackedLinearRows(model_, diags_)) { ok_ = false; }
        if (!validatePackedScalarModel(model_, diags_)) { ok_ = false; }
        checkFunctionBodies();
        checkFunctionAcyclicity();
        for (const auto& c : model_.constraints) {
            checkConstraint(c);
        }
        checkObjectives();
        return ok_;
    }

    bool runTerms(const std::vector<LocatedExpr>& terms, const std::string& defaultFile) {
        run();
        // Function bodies checked by run() have local binders. Start the batch
        // in a fresh global scope, then share successes only within this call.
        Detail::clearExpressionRootCache(check_cache_);
        scope_epoch_ = ++next_scope_epoch_;
        retain_root_cache_ = true;
        SourceLoc fallback{defaultFile, 0, 0};
        for (const auto& term : terms) {
            fallback.line = term.loc.line;
            fallback.column = term.loc.column;
            const auto& location = term.loc.file.empty() ? fallback : term.loc;
            if (!checkExpr(term.expression, location)) { ok_ = false; }
        }
        return ok_;
    }

private:
    void error(const std::string& msg, const SourceLoc& loc,
               ErrorCode code = ErrorCode::E_TYPE) {
        diags_.error(code, msg, loc);
        ok_ = false;
    }

    void checkUninterpretedSorts() {
        for (const auto& sort : model_.uninterpreted_sorts) {
            if (sort.name.empty()) {
                error("an uninterpreted sort declaration has no name", sort.loc,
                      ErrorCode::E_INTERNAL);
                continue;
            }
            if (!uninterpreted_sorts_.emplace(sort.name, sort.arity).second) {
                error("uninterpreted sort '" + sort.name
                          + "' is declared more than once", sort.loc);
            }
        }
    }

    void checkFuns() {
        for (const auto& f : model_.funs) {
            if (f.name.empty()) {
                error("a function declaration has no name", f.loc,
                      ErrorCode::E_INTERNAL);
                continue;
            }
            if (functions_.count(f.name) != 0) {
                error("function '" + f.name + "' is declared more than once", f.loc);
                continue;
            }
            // A function and a variable of the same name would be two symbols
            // the emitted script cannot tell apart.
            if (declared_.count(f.name) != 0) {
                error("'" + f.name + "' is declared both as a variable and as a "
                                     "function", f.loc);
                continue;
            }
            functions_.emplace(f.name, &f);
            for (const Sort& argument : f.params) {
                checkDatatypeSortReferences(argument, {}, f.loc,
                                            "function '" + f.name + "' parameter");
            }
            checkDatatypeSortReferences(f.result, {}, f.loc,
                                        "function '" + f.name + "' result");
        }
    }

    void checkFunctionBodies() {
        for (const auto& f : model_.funs) {
            if (!f.body) {
                if (f.auxiliary) {
                    error("target-only auxiliary function '" + f.name
                              + "' must have a definition",
                          f.loc, ErrorCode::E_INTERNAL);
                }
                if (!f.binders.empty()) {
                    error("uninterpreted function '" + f.name
                              + "' has parameter binders but no body", f.loc,
                          ErrorCode::E_INTERNAL);
                }
                continue;
            }
            bool contains_global = false;
            std::unordered_set<const Expr*> inspected;
            std::vector<const Expr*> pending{f.body.get()};
            while (!pending.empty()) {
                const auto* expression = pending.back();
                pending.pop_back();
                if (!expression || !inspected.insert(expression).second) { continue; }
                contains_global = contains_global || expression->kind == ExprKind::GLOBAL;
                for (const auto& child : expression->args) { pending.push_back(child.get()); }
            }
            if (contains_global) {
                error("defined function '" + f.name
                          + "' contains a global constraint; global decomposition inside function "
                            "bodies is not supported",
                      f.loc);
                continue;
            }
            if (f.binders.size() != f.params.size()) {
                error("defined function '" + f.name + "' has "
                          + std::to_string(f.binders.size()) + " binder(s), but its signature has "
                          + std::to_string(f.params.size()) + " parameter(s)",
                      f.loc, ErrorCode::E_INTERNAL);
                continue;
            }
            std::unordered_set<std::string> names;
            bool binders_ok = true;
            for (std::size_t i = 0; i < f.binders.size(); ++i) {
                const Binder& binder = f.binders[i];
                if (binder.name.empty() || !names.insert(binder.name).second) {
                    error("defined function '" + f.name
                              + "' has an empty or duplicate parameter name",
                          f.loc, ErrorCode::E_INTERNAL);
                    binders_ok = false;
                    continue;
                }
                if (!sameSort(binder.sort, f.params[i])) {
                    error("parameter '" + binder.name + "' of defined function '"
                              + f.name + "' has sort " + toString(binder.sort)
                              + " but the signature says " + toString(f.params[i]),
                          f.loc, ErrorCode::E_INTERNAL);
                    binders_ok = false;
                }
                checkDatatypeSortReferences(binder.sort, {}, f.loc,
                                            "function '" + f.name + "' parameter binder");
            }
            if (!binders_ok) { continue; }

            // Function parameters are lexical binders and may shadow globals,
            // just as SMT-LIB define-fun parameters do. BOUND_VAR is distinct
            // from IDENT, so free occurrences continue to resolve globally.
            for (const Binder& binder : f.binders) {
                bound_.emplace(binder.name, binder.sort);
            }
            const bool body_ok = checkExpr(f.body, f.loc);
            for (const Binder& binder : f.binders) { bound_.erase(binder.name); }
            if (body_ok && !sameSort(f.body->sort, f.result)) {
                error("body of defined function '" + f.name + "' has sort "
                          + toString(f.body->sort) + " but the signature returns "
                          + toString(f.result),
                      locOf(f.body, f.loc));
            }
        }
    }

    void checkFunctionAcyclicity() {
        std::unordered_map<std::string, std::vector<std::string>> edges;
        for (const auto& f : model_.funs) {
            if (!f.body) {
                if (!f.recursive_group.empty()) {
                    error("uninterpreted function '" + f.name
                              + "' cannot belong to a recursive definition group", f.loc);
                }
                continue;
            }
            std::unordered_set<const Expr*> seen;
            std::vector<ExprPtr> pending{f.body};
            while (!pending.empty()) {
                ExprPtr expression = std::move(pending.back());
                pending.pop_back();
                if (!expression || !seen.insert(expression.get()).second) continue;
                if (expression->kind == ExprKind::APPLY) {
                    const auto dependency = functions_.find(expression->name);
                    if (dependency != functions_.end() && dependency->second->body) {
                        edges[f.name].push_back(expression->name);
                    }
                }
                for (const ExprPtr& child : expression->args) {
                    if (child) pending.push_back(child);
                }
            }
        }

        // Strongly connected components are the exact units that SMT-LIB
        // binds together with define-funs-rec. A caller cannot opt only one
        // edge into recursion: every member of the component must carry the
        // same explicit label, and that label cannot include unrelated defs.
        std::unordered_map<std::string, std::size_t> index;
        std::unordered_map<std::string, std::size_t> lowlink;
        std::unordered_set<std::string> on_stack;
        std::vector<std::string> stack;
        std::vector<std::vector<std::string>> components;
        std::size_t next_index = 0;
        struct CallFrame { std::string name; std::size_t next_dependency = 0; };
        for (const auto& f : model_.funs) {
            if (!f.body || index.find(f.name) != index.end()) { continue; }
            std::vector<CallFrame> pending;
            const auto enter = [&](const std::string& name) {
                index[name] = lowlink[name] = next_index++;
                stack.push_back(name);
                on_stack.insert(name);
                pending.push_back({name});
            };
            enter(f.name);
            while (!pending.empty()) {
                auto& frame = pending.back();
                const std::string name = frame.name;
                if (frame.next_dependency < edges[name].size()) {
                    const std::string dependency = edges[name][frame.next_dependency++];
                    if (index.find(dependency) == index.end()) {
                        enter(dependency);
                    } else if (on_stack.find(dependency) != on_stack.end()) {
                        lowlink[name] = std::min(lowlink[name], index[dependency]);
                    }
                    continue;
                }
                if (lowlink[name] == index[name]) {
                    std::vector<std::string> component;
                    while (!stack.empty()) {
                        std::string member = std::move(stack.back());
                        stack.pop_back();
                        on_stack.erase(member);
                        component.push_back(member);
                        if (member == name) { break; }
                    }
                    components.push_back(std::move(component));
                }
                pending.pop_back();
                if (!pending.empty()) {
                    auto& parent = lowlink[pending.back().name];
                    parent = std::min(parent, lowlink[name]);
                }
            }
        }

        std::unordered_map<std::string, const FunDecl*> declarations;
        for (const auto& f : model_.funs) declarations.emplace(f.name, &f);
        std::unordered_map<std::string, std::size_t> component_for_group;
        for (std::size_t component_index = 0;
             component_index < components.size(); ++component_index) {
            const auto& component = components[component_index];
            const bool self_recursive = component.size() == 1
                && std::find(edges[component.front()].begin(),
                             edges[component.front()].end(), component.front())
                       != edges[component.front()].end();
            const bool recursive = component.size() > 1 || self_recursive;
            std::string group;
            bool consistent = true;
            for (const auto& member : component) {
                const auto declaration = declarations.find(member);
                if (declaration == declarations.end()) continue;
                const std::string& candidate = declaration->second->recursive_group;
                if (candidate.empty()) { consistent = false; }
                else if (group.empty()) { group = candidate; }
                else if (group != candidate) { consistent = false; }
            }
            if (recursive && (!consistent || group.empty())) {
                const auto declaration = declarations.find(component.front());
                error("recursive or cyclic HIR function definition requires one explicit recursive_group label",
                      declaration == declarations.end() ? SourceLoc{} : declaration->second->loc);
            } else if (!recursive && std::any_of(
                           component.begin(), component.end(), [&](const std::string& member) {
                               const auto declaration = declarations.find(member);
                               return declaration != declarations.end()
                                      && !declaration->second->recursive_group.empty();
                           })) {
                const auto declaration = declarations.find(component.front());
                error("recursive_group label does not name a recursive call component",
                      declaration == declarations.end() ? SourceLoc{} : declaration->second->loc);
            }
            if (recursive && consistent && !group.empty()) {
                const auto prior = component_for_group.emplace(group, component_index);
                if (!prior.second && prior.first->second != component_index) {
                    const auto declaration = declarations.find(component.front());
                    error("one recursive_group label cannot name multiple call components",
                          declaration == declarations.end() ? SourceLoc{} : declaration->second->loc);
                }
            }
        }
    }

    void checkDecls() {
        declared_.reserve(model_.decls.size());
        for (const auto& d : model_.decls) {
            if (d.name.empty()) {
                error("a declaration has no name", d.loc, ErrorCode::E_INTERNAL);
                continue;
            }
            const auto prior = declared_.find(d.name);
            if (prior != declared_.end()) {
                // Silently keeping the last one is how `var int: x; var bool: x;`
                // used to translate: one declare-fun, the other declaration and
                // everything it implied simply gone.
                error("'" + d.name + "' is declared more than once (first as "
                          + toString(*prior->second) + ", again as "
                          + toString(d.sort) + ")",
                      d.loc);
                continue;
            }
            if (functions_.count(d.name) != 0) {
                error("'" + d.name + "' is declared both as a function and as a "
                                     "variable", d.loc);
                continue;
            }
            declared_.emplace(d.name, &d.sort);
            checkDatatypeSortReferences(d.sort, {}, d.loc,
                                        "declaration '" + d.name + "'");
        }

        // Bounds constrain variables in one model; they are not sequential
        // definitions. Register every declaration before resolving a bound so
        // reordering declarations cannot change whether its references exist.
        for (const auto& d : model_.decls) {
            if (!d.lower_bound && !d.upper_bound) { continue; }
            const auto declared = declared_.find(d.name);
            // Keep the original rejection/skip policy for missing names,
            // duplicate declarations and function/variable name collisions.
            if (declared == declared_.end() || declared->second != &d.sort) {
                continue;
            }
            for (const auto* bound : {&d.lower_bound, &d.upper_bound}) {
                if (!*bound) { continue; }
                const bool is_lower = (bound == &d.lower_bound);
                if (!checkExpr(*bound, d.loc)) { continue; }
                if (!isNumeric(d.sort.kind)) {
                    error(std::string(is_lower ? "lower" : "upper")
                              + " bound on '" + d.name + "', which is "
                              + toString(d.sort) + " and has no order",
                          locOf(*bound, d.loc));
                } else if (!isNumeric((*bound)->sort.kind)) {
                    error(std::string(is_lower ? "lower" : "upper")
                              + " bound on '" + d.name + "' is "
                              + toString((*bound)->sort) + ", not numeric",
                          locOf(*bound, d.loc));
                }
            }
        }
    }

    void checkPackedBoolClauses() {
        const auto isSimplePrefix=[](const std::string& prefix) {
            if (prefix.empty()) return false;
            const auto first=[](unsigned char c) {
                return (c>='A'&&c<='Z')||(c>='a'&&c<='z')||c=='_';
            };
            const auto rest=[&](unsigned char c) {
                return first(c)||(c>='0'&&c<='9')||c=='-';
            };
            if (!first(static_cast<unsigned char>(prefix.front()))) return false;
            return std::all_of(prefix.begin()+1,prefix.end(),[&](unsigned char c){return rest(c);});
        };
        const auto nameInAnyRange=[&](std::string_view name) {
            for (const BoolVarRange& range : model_.bool_var_ranges)
                if (range.contains(std::string(name))) return true;
            return false;
        };
        for (std::size_t i=0;i<model_.bool_var_ranges.size();++i) {
            const BoolVarRange& range=model_.bool_var_ranges[i];
            if (!isSimplePrefix(range.prefix) || range.first==0
                || range.sort.kind!=SortKind::BOOL
                || (range.count!=0 && range.count-1>std::numeric_limits<std::uint64_t>::max()-range.first)) {
                error("packed Bool variable range has an invalid prefix, interval, or sort",range.loc,ErrorCode::E_INTERNAL);
                continue;
            }
            for (std::size_t j=0;j<i;++j) {
                const BoolVarRange& prior=model_.bool_var_ranges[j];
                const bool same_prefix=range.prefix==prior.prefix;
                const bool nested_prefix=range.prefix.compare(0,prior.prefix.size(),prior.prefix)==0
                    || prior.prefix.compare(0,range.prefix.size(),range.prefix)==0;
                bool overlap=false;
                if (same_prefix && range.count && prior.count) {
                    const std::uint64_t a_end=range.first+range.count-1;
                    const std::uint64_t b_end=prior.first+prior.count-1;
                    overlap=range.first<=b_end&&prior.first<=a_end;
                } else if (nested_prefix) {
                    // Distinct prefix intervals with nested textual namespaces
                    // are rejected so generated names cannot alias.
                    overlap=true;
                }
                if (overlap) error("packed Bool variable ranges have overlapping generated symbol namespaces",range.loc);
            }
        }
        for (const auto& item:declared_) if (nameInAnyRange(item.first))
            error("packed Bool variable range collides with declaration '"+std::string(item.first)+"'",{});
        for (const auto& item:functions_) if (nameInAnyRange(item.first))
            error("packed Bool variable range collides with function '"+item.first+"'",item.second->loc);
        for (const auto& item:datatypes_) if (nameInAnyRange(item.first))
            error("packed Bool variable range collides with datatype '"+item.first+"'",item.second->loc);
        for (const auto& item:constructors_) if (nameInAnyRange(item.first))
            error("packed Bool variable range collides with constructor '"+item.first+"'",item.second.first->loc);
        for (const auto& item:selectors_) if (nameInAnyRange(item.first))
            error("packed Bool variable range collides with selector '"+item.first+"'",item.second.first->loc);
        for (const auto& item:uninterpreted_sorts_) if (nameInAnyRange(item.first))
            error("packed Bool variable range collides with sort '"+item.first+"'",{});
        for (const Objective& objective:model_.objectives)
            if (!objective.name.empty()&&nameInAnyRange(objective.name))
                error("packed Bool variable range collides with objective '"+objective.name+"'",objective.loc);

        for (const PackedBoolClauseBatch& batch:model_.packed_bool_clauses) {
            if (batch.variable_range>=model_.bool_var_ranges.size()) {
                error("packed Boolean clause batch refers to a missing variable range",{} ,ErrorCode::E_INTERNAL);
                continue;
            }
            const BoolVarRange& range=model_.bool_var_ranges[batch.variable_range];
            const std::size_t clauses=batch.source_lines.size();
            if (batch.clause_offsets.size()!=clauses+1||batch.weight_offsets.size()!=clauses+1) {
                error("packed Boolean clause offsets must have one entry per clause plus a sentinel",range.loc,ErrorCode::E_INTERNAL);
                continue;
            }
            if (batch.clause_offsets.front()!=0||batch.clause_offsets.back()!=batch.literals.size())
                error("packed Boolean clause offsets do not span the literal pool",range.loc,ErrorCode::E_INTERNAL);
            if (batch.weight_offsets.front()!=0||batch.weight_offsets.back()!=batch.weight_bytes.size())
                error("packed Boolean weight offsets do not span the exact-weight pool",range.loc,ErrorCode::E_INTERNAL);
            for (std::size_t i=0;i<clauses;++i) {
                SourceLoc loc{batch.source_file,static_cast<int>(std::min<std::uint32_t>(batch.source_lines[i],static_cast<std::uint32_t>(std::numeric_limits<int>::max()))),1};
                const auto begin=batch.clause_offsets[i],end=batch.clause_offsets[i+1];
                const auto wb=batch.weight_offsets[i],we=batch.weight_offsets[i+1];
                if (begin>end||end>batch.literals.size()) { error("packed Boolean clause has invalid literal offsets",loc,ErrorCode::E_INTERNAL); continue; }
                if (wb>we||we>batch.weight_bytes.size()) { error("packed Boolean clause has invalid weight offsets",loc,ErrorCode::E_INTERNAL); continue; }
                if (batch.source_lines[i]==0||batch.source_lines[i]>static_cast<std::uint32_t>(std::numeric_limits<int>::max()))
                    error("packed Boolean clause source line is outside SourceLoc range",loc,ErrorCode::E_INTERNAL);
                if (wb<we) {
                    bool nonzero=false;
                    if (we-wb>1&&batch.weight_bytes[wb]=='0') error("packed soft weight has a leading zero",loc);
                    for (std::uint64_t j=wb;j<we;++j) {
                        const char c=batch.weight_bytes[static_cast<std::size_t>(j)];
                        if (c<'0'||c>'9') { error("packed soft weight is not an exact decimal numeral",loc); break; }
                        nonzero=nonzero||(c!='0');
                    }
                    if (!nonzero) error("packed soft weight must be positive",loc);
                }
                for (std::uint64_t j=begin;j<end;++j) {
                    const std::int64_t literal=batch.literals[static_cast<std::size_t>(j)];
                    if (literal==0||literal==std::numeric_limits<std::int64_t>::min()) {
                        error("packed Boolean clause contains a zero or overflowing literal",loc); continue;
                    }
                    const std::uint64_t magnitude=literal<0
                        ? static_cast<std::uint64_t>(-(literal+1))+1
                        : static_cast<std::uint64_t>(literal);
                    if (magnitude==0||magnitude>range.count)
                        error("packed Boolean literal is outside its variable range",loc);
                }
            }
        }
    }

    void checkConstraint(const Constraint& c) {
        if (c.soft) {
            if (!c.weight_text.empty() && !isExactPositiveSoftWeight(c.weight_text))
                error("exact soft weight must be a positive integer decimal string", c.loc);
            if (c.weight_text.empty() && (!std::isfinite(c.weight) || c.weight <= 0.0))
                error("soft weight must be finite and positive", c.loc);
            if (!isSoftGroupSymbol(c.group))
                error("soft group must be empty or a valid SMT-LIB symbol spelling", c.loc);
        }
        if (!c.formula) {
            error("a constraint has no formula", c.loc, ErrorCode::E_INTERNAL);
            return;
        }
        if (!checkExpr(c.formula, c.loc)) { return; }
        if (c.formula->sort.kind != SortKind::BOOL) {
            error(std::string("a constraint must be Bool, but this one is ")
                      + toString(c.formula->sort),
                  locOf(c.formula, c.loc));
        }
    }

    void checkObjectives() {
        // Two or more objectives without a stated combination is not "several
        // independent objectives" -- it is a question nobody asked. The emitter
        // would produce several (minimize t) commands, whose documented meaning
        // under Z3 is lexicographic, so silence here picks a semantics rather
        // than deferring one. A frontend that means independent optima writes
        // BOX; one that has not decided gets an error instead of a default.
        const std::size_t count = objectiveCountWithSoft(model_);
        const bool several = count >= 2;
        const bool combined =
            model_.objective_combination != ObjectiveCombination::SINGLE;
        if (several && !combined) {
            error("this model has " + std::to_string(count)
                      + " objectives but no combination; set "
                        "ConstraintModel::objective_combination to say how they "
                        "relate (lexicographic, pareto, box, minmax, maxmin)",
                  model_.objectives.empty() ? SourceLoc{} : model_.objectives.front().loc, ErrorCode::E_INTERNAL);
        }
        if (!several && combined) {
            error(std::string("objective_combination is '")
                      + objectiveCombinationName(model_.objective_combination)
                      + "' but the model has "
                      + std::to_string(count)
                      + " objective(s); a combination needs at least two",
                  model_.objectives.empty() ? SourceLoc{}
                                            : model_.objectives.front().loc,
                  ErrorCode::E_INTERNAL);
        }

        std::unordered_set<std::string> seen;
        for (const auto& o : model_.objectives) {
            if (!o.term) {
                error("an objective has no term", o.loc, ErrorCode::E_INTERNAL);
                continue;
            }
            if (checkExpr(o.term, o.loc) && !isNumeric(o.term->sort.kind)) {
                // Minimising a Bool has no meaning to a solver: it emits
                // (minimize b), which every OMT solver rejects or, worse,
                // reinterprets.
                error(std::string("an objective must be numeric, but this one is ")
                          + toString(o.term->sort),
                      locOf(o.term, o.loc));
            }
            if (o.name.empty()) { continue; }
            // A name is what the emitted (define-objective NAME ...) binds. If
            // it is also a variable's name the script declares one symbol and
            // then rebinds it as an objective, which is a different model than
            // the one that was translated. The frontend that minted the name is
            // at fault, so this is E_INTERNAL, not E_TYPE.
            if (declared_.count(o.name) != 0) {
                error("objective name '" + o.name
                          + "' collides with the variable of the same name",
                      o.loc, ErrorCode::E_INTERNAL);
            }
            if (!seen.insert(o.name).second) {
                error("two objectives are both named '" + o.name + "'",
                      o.loc, ErrorCode::E_INTERNAL);
            }
        }
    }

    /** @return false once this subtree has produced a diagnostic, so callers do
     *  not pile a consequence on top of the cause. */
    bool checkExpr(const ExprPtr& e, const SourceLoc& fallback) {
        // HIR is allowed to be a DAG. Remember successful nodes while
        // checking one expression root (or an explicit immutable term batch),
        // keyed by lexical scope epoch as well as address: the same BOUND_VAR
        // node can occur under different binders. Ordinary model checking
        // bounds cache memory to one root; batch roots stay alive for the call.
        if (expr_depth_ == 0 && !retain_root_cache_) {
            Detail::clearExpressionRootCache(check_cache_);
            scope_epoch_ = ++next_scope_epoch_;
        }
        if (e) {
            if (check_cache_.count({e.get(), scope_epoch_})) { return true; }
        }
        struct DepthGuard {
            std::size_t& depth;
            explicit DepthGuard(std::size_t& d) : depth(d) { ++depth; }
            ~DepthGuard() { --depth; }
        } depth_guard(expr_depth_);

        // Check ordinary DAG operands bottom-up. Calling checkOp recursively
        // for each gate exhausted the native stack on valid AIGER circuits.
        // Scope entry and exit are worklist events too: nested quantifiers
        // must not re-enter this function recursively.
        struct QuantifierScope {
            std::vector<std::string> added;
            std::size_t enclosing_scope;
        };
        struct Pending {
            const ExprPtr* expression;
            const SourceLoc* fallback;
            std::size_t next_argument = 0;
            std::unique_ptr<QuantifierScope> quantifier{};
        };
        std::vector<Pending> pending;
        pending.push_back({&e, &fallback});
        const auto leave_scope = [&](Pending& frame) {
            if (!frame.quantifier) { return; }
            for (const auto& name : frame.quantifier->added) { bound_.erase(name); }
            scope_epoch_ = frame.quantifier->enclosing_scope;
            frame.quantifier.reset();
        };
        const auto fail = [&]() {
            while (!pending.empty()) { leave_scope(pending.back()); pending.pop_back(); }
            return false;
        };
        std::unordered_set<const Expr*> active;
        if (e) { active.insert(e.get()); }
        while (!pending.empty()) {
            auto& frame = pending.back();
            const auto& node = *frame.expression;
            const auto& loc = node ? locOf(node, *frame.fallback) : *frame.fallback;
            const bool quantified = node && (node->kind == ExprKind::FORALL || node->kind == ExprKind::EXISTS);
            if (quantified && !frame.quantifier) {
                frame.quantifier = std::make_unique<QuantifierScope>();
                frame.quantifier->enclosing_scope = scope_epoch_;
                if (!enterQuantifier(node, loc, frame.quantifier->added)) { return fail(); }
                scope_epoch_ = ++next_scope_epoch_;
            }
            const bool ordinary = node && (node->kind == ExprKind::OP
                || node->kind == ExprKind::APPLY || node->kind == ExprKind::GLOBAL
                || node->kind == ExprKind::DT_CONSTRUCTOR
                || node->kind == ExprKind::DT_SELECTOR || node->kind == ExprKind::DT_TESTER);
            if ((ordinary || quantified) && frame.next_argument < node->args.size()) {
                const auto& child = node->args[frame.next_argument++];
                if (child) {
                    if (check_cache_.count({child.get(), scope_epoch_})) { continue; }
                    if (!active.insert(child.get()).second) {
                        error("a cyclic expression is in the model", loc, ErrorCode::E_INTERNAL);
                        return fail();
                    }
                }
                pending.push_back({&child, &loc});
                continue;
            }
            if (quantified) {
                if (!finishQuantifier(node, loc)) { return fail(); }
                leave_scope(frame);
            } else if (!checkExprUncached(node, *frame.fallback)) { return fail(); }
            if (node) {
                // Even an unshared operand must be cached here: the local
                // operator rule asks for it again after its worklist visit.
                check_cache_.insert({node.get(), scope_epoch_});
                active.erase(node.get());
            }
            pending.pop_back();
        }
        return true;
    }

    bool checkedOperand(const ExprPtr& e, const SourceLoc& fallback) {
        if (check_cache_.count({e.get(), scope_epoch_})) { return true; }
        // A local rule only consults completed worklist entries. Scope belongs
        // in the key: a shared expression may be visited both outside and
        // inside a quantifier before its parent's local rule runs.
        error("expression operand missing from type-checking worklist",
              e ? locOf(e, fallback) : fallback, ErrorCode::E_INTERNAL);
        return false;
    }

    bool checkExprUncached(const ExprPtr& e, const SourceLoc& fallback) {
        if (!e) {
            error("a null expression is in the model", fallback, ErrorCode::E_INTERNAL);
            return false;
        }
        const SourceLoc& loc = locOf(e, fallback);

        switch (e->kind) {
        case ExprKind::LIT_BOOL:
            if (e->sort.kind != SortKind::BOOL) {
                error(std::string("a Bool literal carries sort ")
                          + toString(e->sort), loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;

        case ExprKind::LIT_INT: {
            if (e->sort.kind != SortKind::INT) {
                error(std::string("an integer literal carries sort ")
                          + toString(e->sort), loc, ErrorCode::E_INTERNAL);
                return false;
            }
            // The decimal text is authoritative -- int_value is valid only when
            // the literal fits -- and it reaches the emitted script, so a
            // literal that is not a numeral must be refused here rather than
            // printed and rejected by whatever reads the output.
            static const std::regex kInteger(R"(^[+-]?\d+$)");
            if (!e->name.empty() && !std::regex_match(e->name, kInteger)) {
                error("'" + e->name + "' is not an integer numeral", loc);
                return false;
            }
            return true;
        }

        case ExprKind::IDENT: {
            const auto it = declared_.find(e->name);
            if (it == declared_.end()) {
                if (const auto range = scalar_ranges_.find(e->name)) {
                    if (!sameSort(range->sort, e->sort)) {
                        error("'" + e->name + "' has the wrong compact scalar sort", loc);
                        return false;
                    }
                    return true;
                }
                bool found=false;
                for (const BoolVarRange& range:model_.bool_var_ranges) {
                    if (range.contains(e->name)) {
                        found=true;
                        if (!sameSort(range.sort,e->sort)) {
                            error("'"+e->name+"' is used as "+toString(e->sort)+" but its packed range is "+toString(range.sort),loc);
                            return false;
                        }
                        return true;
                    }
                }
                if (!found) error("undeclared identifier '" + e->name + "'", loc);
                return false;
            }
            if (!sameSort(*it->second, e->sort)) {
                // The frontend resolved the name against a stale scope or
                // retained only the outer sort kind. Full sorts carry identity:
                // BV widths, array indices/elements, and parametric sort
                // arguments all affect the emitted term's meaning and type.
                error("'" + e->name + "' is used as " + toString(e->sort)
                          + " but was declared " + toString(*it->second),
                      loc);
                return false;
            }
            return true;
        }

        case ExprKind::BOUND_VAR: {
            const auto it = bound_.find(e->name);
            if (it == bound_.end()) {
                error("bound variable '" + e->name
                          + "' is not bound by any enclosing quantifier", loc);
                return false;
            }
            if (!sameSort(it->second, e->sort)) {
                error("bound variable '" + e->name + "' is used as "
                          + toString(e->sort) + " but was bound as "
                          + toString(it->second),
                      loc);
                return false;
            }
            return true;
        }

        case ExprKind::FORALL:
        case ExprKind::EXISTS:
            error("quantifier bypassed scoped checking worklist", loc, ErrorCode::E_INTERNAL);
            return false;

        case ExprKind::LIT_BITVEC:
            if (e->sort.kind != SortKind::BITVEC) {
                error("a bit-vector literal carries sort "
                          + toString(e->sort),
                      loc, ErrorCode::E_INTERNAL);
                return false;
            }
            if (e->sort.width == 0) {
                error("a bit-vector literal has width 0", loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;

        case ExprKind::LIT_STRING:
            if (e->sort.kind != SortKind::STRING) {
                error("a string literal carries sort "
                          + toString(e->sort),
                      loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;

        case ExprKind::APPLY:
            return checkApply(e, loc);

        case ExprKind::DT_CONSTRUCTOR:
            return checkDtConstructor(e, loc);
        case ExprKind::DT_SELECTOR:
            return checkDtSelector(e, loc);
        case ExprKind::DT_TESTER:
            return checkDtTester(e, loc);

        case ExprKind::GLOBAL:
            return checkGlobal(e, loc);

        case ExprKind::LIT_REAL:
        case ExprKind::LIT_FLOAT: {
            const SortKind want = e->kind == ExprKind::LIT_REAL
                                      ? SortKind::REAL : SortKind::FLOAT;
            if (e->sort.kind != want) {
                error(std::string("a ")
                          + (e->kind == ExprKind::LIT_REAL ? "real" : "floating-point")
                          + " literal records sort " + toString(e->sort),
                      loc, ErrorCode::E_INTERNAL);
                return false;
            }
            // The text reaches the engine's builder and then the script, so a
            // literal that is not a numeral must be refused here rather than
            // emitted and rejected by whatever reads the output.
            // Decimal, or an exact rational `a/b`. lp.md §4.1 asks for the
            // rational form by name: an LP coefficient of 1/3 has no decimal
            // spelling, and rounding it answers a different question while
            // reporting Fidelity::exact(). A float literal takes only the
            // decimal form -- `1/3` at single precision is not a value, it is a
            // rounding waiting to happen, and which rounding is the caller's to
            // state.
            static const std::regex kDecimal(R"(^[+-]?\d+(\.\d+)?$)");
            static const std::regex kRational(R"(^[+-]?\d+/\d+$)");
            // A Float has two more spellings, and they are the only two an
            // SMT-LIB script can actually contain: the bit triple `(fp #b0 #b…
            // #b…)` and the five special values, whose whole point is that they
            // have no decimal form -- NaN is not a number and infinity is not a
            // numeral. Accepting the decimal alone meant this rule admitted
            // exactly the spellings that are not legal Float literals and
            // refused exactly the ones that are, so every literal read back out
            // of a script was rejected.
            //
            // The decimal stays legal because a frontend may build one directly
            // -- MiniZinc's `1.5` at float32 -- and the engine's mkConstFp
            // converts it to the triple on the way out.
            static const std::regex kFpTriple(
                R"(^\(fp #b[01]+ #b[01]+ #b[01]+\)$)");
            static const std::regex kFpSpecial(
                R"(^\(_ (\+oo|-oo|\+zero|-zero|NaN) (\d+) (\d+)\)$)");
            std::smatch special;
            const bool is_special = e->kind == ExprKind::LIT_FLOAT
                && std::regex_match(e->name, special, kFpSpecial);
            const bool isRational = e->kind == ExprKind::LIT_REAL
                && std::regex_match(e->name, kRational);
            // A literal denotes one exact number. SMT division is total, but
            // its unspecified value at zero cannot represent a rational
            // literal. Inspect digits without imposing a machine-integer bound.
            if (isRational
                && e->name.find_first_not_of('0', e->name.find('/') + 1)
                       == std::string::npos) {
                error("an exact rational literal requires a nonzero denominator", loc);
                return false;
            }
            const bool ok = std::regex_match(e->name, kDecimal)
                || isRational
                || (e->kind == ExprKind::LIT_FLOAT
                    && std::regex_match(e->name, kFpTriple))
                || is_special;
            if (!ok) {
                error("'" + e->name + "' is not a "
                          + (e->kind == ExprKind::LIT_REAL
                                 ? "decimal numeral or exact rational a/b"
                                 : "decimal numeral, an (fp #b.. #b.. #b..) "
                                   "triple, or a special value such as "
                                   "(_ NaN 8 24)"),
                      loc);
                return false;
            }
            if (e->kind == ExprKind::LIT_REAL) {
                const auto slash = e->name.find('/');
                // This is an exact numeral, not the total SMT-LIB division
                // operator. Check the digit string without a bounded integer
                // conversion so arbitrarily large denominators stay legal.
                if (slash != std::string::npos
                    && e->name.find_first_not_of('0', slash + 1) == std::string::npos) {
                    error("an exact rational literal must have a nonzero denominator", loc);
                    return false;
                }
            }
            // A special value names its own format, so the two can disagree:
            // `(_ NaN 11 53)` recorded at Float32 would emit a script whose
            // literal contradicts the sort the term was checked against, and
            // the engine reading it back would build a different value.
            if (is_special
                && (special[2].str() != std::to_string(e->sort.exponent_bits)
                    || special[3].str() != std::to_string(e->sort.significand_bits))) {
                error("'" + e->name + "' names a format that is not "
                          + toString(e->sort), loc);
                return false;
            }
            if (e->kind == ExprKind::LIT_FLOAT
                && (e->sort.exponent_bits == 0 || e->sort.significand_bits == 0)) {
                error("a floating-point literal has format "
                          + toString(e->sort), loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }

        case ExprKind::LIT_SET: {
            if (e->sort.kind != SortKind::SET || !e->sort.elem) {
                error("a set constant records sort " + toString(e->sort), loc,
                      ErrorCode::E_INTERNAL);
                return false;
            }
            if (e->name != "set.empty" && e->name != "set.universe") {
                error("'" + e->name + "' is not a set constant; SMT-LIB has "
                      "set.empty and set.universe", loc);
                return false;
            }
            return true;
        }

        case ExprKind::LIT_TUPLE_UNIT: {
            // `UnitTuple` is the EMPTY tuple sort, so the check is that the
            // field list is empty and not merely that the kind is TUPLE: a
            // `tuple.unit` recording `(Tuple Int)` would be a value of a sort
            // that has no such value, and it would lower into a script whose
            // declared sort and asserted term disagree.
            if (e->sort.kind != SortKind::TUPLE || !e->sort.args.empty()) {
                error("'tuple.unit' records sort " + toString(e->sort)
                          + ", not UnitTuple", loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }

        case ExprKind::LIT_REGLAN: {
            if (e->sort.kind != SortKind::REGLAN) {
                error("a regular-expression constant records sort "
                          + toString(e->sort), loc, ErrorCode::E_INTERNAL);
                return false;
            }
            static const char* kConsts[] = {"re.none", "re.all", "re.allchar"};
            for (const char* c : kConsts) {
                if (e->name == c) { return true; }
            }
            error("'" + e->name + "' is not a nullary regular expression; "
                  "SMT-LIB has re.none, re.all and re.allchar", loc);
            return false;
        }

        case ExprKind::LIT_ROUNDING_MODE: {
            if (e->sort.kind != SortKind::ROUNDING_MODE) {
                error("a rounding-mode literal records sort " + toString(e->sort),
                      loc, ErrorCode::E_INTERNAL);
                return false;
            }
            // The engine's builder takes the mode as a string, so an
            // unrecognised name would be emitted verbatim into the script and
            // rejected by whatever reads it -- a failure three layers from its
            // cause. SMT-LIB names exactly five.
            static const char* kModes[] = {"RNE", "RNA", "RTP", "RTN", "RTZ"};
            for (const char* m : kModes) {
                if (e->name == m) { return true; }
            }
            error("'" + e->name + "' is not a rounding mode; SMT-LIB has "
                  "RNE, RNA, RTP, RTN and RTZ", loc);
            return false;
        }

        case ExprKind::OP:
            return checkOp(e, loc);
        }

        error("an expression has an unknown kind", loc, ErrorCode::E_INTERNAL);
        return false;
    }

    bool enterQuantifier(const ExprPtr& e, const SourceLoc& loc,
                         std::vector<std::string>& added) {
        if (e->binders.empty()) {
            error("a quantifier binds no variables", loc, ErrorCode::E_INTERNAL);
            return false;
        }
        if (e->args.size() != 1 || !e->args[0]) {
            error("a quantifier has no body", loc, ErrorCode::E_INTERNAL);
            return false;
        }
        // Shadowing is legal in SMT-LIB and confusing everywhere, so it is
        // rejected: a frontend that emits it is almost certainly reusing a name
        // by accident, and the alternative -- silently taking the inner one --
        // makes the resulting formula depend on a scoping rule nobody wrote.
        bool ok = true;
        for (const auto& b : e->binders) {
            if (b.name.empty()) {
                error("a quantifier binds a variable with no name", loc,
                      ErrorCode::E_INTERNAL);
                ok = false;
                continue;
            }
            if (bound_.count(b.name) != 0 || declared_.count(b.name) != 0) {
                error("quantifier binds '" + b.name
                          + "', which is already in scope", loc);
                ok = false;
                continue;
            }
            bound_.emplace(b.name, b.sort);
            added.push_back(b.name);
        }
        return ok;
    }

    bool finishQuantifier(const ExprPtr& e, const SourceLoc& loc) {
        if (e->args[0]->sort.kind != SortKind::BOOL) {
            error(std::string("a quantifier's body must be Bool, but this one is ")
                      + toString(e->args[0]->sort), loc);
            return false;
        }
        if (e->sort.kind != SortKind::BOOL) {
            error("a quantifier yields Bool, but the expression records " + toString(e->sort),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    bool checkApply(const ExprPtr& e, const SourceLoc& loc) {
        const auto it = functions_.find(e->name);
        if (it == functions_.end()) {
            error("application of undeclared function '" + e->name + "'", loc);
            return false;
        }
        const FunDecl& f = *it->second;
        if (e->args.size() != f.params.size()) {
            error("'" + e->name + "' is declared with "
                      + std::to_string(f.params.size()) + " parameter(s) but applied to "
                      + std::to_string(e->args.size()),
                  loc);
            return false;
        }
        for (std::size_t i = 0; i < e->args.size(); ++i) {
            if (!checkedOperand(e->args[i], loc)) { return false; }
            if (!sameSort(f.params[i], e->args[i]->sort)) {
                error("argument " + std::to_string(i + 1) + " of '" + e->name
                          + "' is " + toString(e->args[i]->sort)
                          + " but the declaration says "
                          + toString(f.params[i]),
                      locOf(e->args[i], loc));
                return false;
            }
        }
        if (!sameSort(f.result, e->sort)) {
            // The recorded sort decides how the term lowers, so a mismatch here
            // is not cosmetic: every consumer trusts it over re-deriving.
            error("'" + e->name + "' returns " + toString(f.result)
                      + " but the application records " + toString(e->sort),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    bool checkGlobal(const ExprPtr& e, const SourceLoc& loc) {
        const GlobalRule* rule = globalRule(e->name);
        if (rule == nullptr) {
            // Thin coverage, not a broken invariant: the input used a global
            // this build has no encoding for.
            error("global constraint '" + e->name + "' is not implemented", loc,
                  ErrorCode::E_UNSUPPORTED_CONSTRUCT);
            return false;
        }
        if (e->args.empty()) {
            if (e->name == "alldifferent_except_0") {
                if (e->sort.kind != SortKind::BOOL) {
                    error("alldifferent_except_0 must yield Bool", loc,
                          ErrorCode::E_INTERNAL);
                    return false;
                }
                return true;
            }
            error("'" + e->name + "' has no arguments; the shape is "
                      + std::string(rule->shape),
                  loc);
            return false;
        }
        for (const auto& a : e->args) {
            if (!checkedOperand(a, loc)) { return false; }
        }
        if (e->name == "connected" || e->name == "dconnected") {
            return checkConnectivityGlobal(e, loc);
        }
        // Which shape, decided by the first argument's sort. checkExpr above
        // has run, so the sorts are trustworthy here and not before.
        const bool indexed = e->args[0]->sort.kind == SortKind::ARRAY;
        const std::size_t want = indexed ? rule->arity : rule->list_min;
        if (want == 0) {
            error("'" + e->name + "' has no " + (indexed ? "indexed" : "list")
                      + " shape; the shape is " + rule->shape,
                  loc);
            return false;
        }
        if (indexed ? (e->args.size() != rule->arity) : (e->args.size() < rule->list_min)) {
            error("'" + e->name + "' takes "
                      + (indexed ? std::to_string(rule->arity)
                                 : ("at least " + std::to_string(rule->list_min)))
                      + " argument(s), not " + std::to_string(e->args.size())
                      + "; the shape is " + rule->shape,
                  loc);
            return false;
        }
        if (e->name == "diffn" || e->name == "diffn_nonstrict") {
            if (!fitsInt64(*e->args[0]) || e->args[0]->int_value <= 0
                || static_cast<unsigned long long>(e->args[0]->int_value)
                    > std::numeric_limits<std::size_t>::max() / 2) {
                error(e->name + " requires a positive constant dimension count", loc);
                return false;
            }
            const auto width = 2 * static_cast<std::size_t>(e->args[0]->int_value);
            if ((e->args.size() - 1) % width != 0) {
                error(e->name + " requires complete position/size pairs for each box", loc);
                return false;
            }
            for (const auto& arg : e->args) {
                if (arg->sort.kind != SortKind::INT) {
                    error(e->name + " requires exact Int arguments", loc);
                    return false;
                }
            }
            if (e->sort.kind != SortKind::BOOL) {
                error(e->name + " must yield Bool", loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }
        if (e->name == "count_value") {
            if (!fitsInt64(*e->args[0]) || e->args[0]->int_value < 0
                || static_cast<unsigned long long>(e->args[0]->int_value) != e->args.size() - 2) {
                error("count_value length disagrees with its term count", loc);
                return false;
            }
            for (std::size_t i = 2; i < e->args.size(); ++i) {
                if (!sameSort(e->args[1]->sort, e->args[i]->sort)) {
                    error("count_value terms must match the sought value's sort", loc);
                    return false;
                }
            }
            if (e->sort.kind != SortKind::INT) {
                error("count_value must yield Int", loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }
        if (e->name == "cumulative") {
            if ((e->args.size() - 1) % 3 != 0) {
                error("cumulative requires capacity followed by start/duration/demand triples", loc);
                return false;
            }
            for (const auto& arg : e->args) {
                if (arg->sort.kind != SortKind::INT) {
                    error("cumulative requires exact Int arguments", loc);
                    return false;
                }
            }
            if (e->sort.kind != SortKind::BOOL) {
                error("cumulative must yield Bool", loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }
        if (e->name == "table" || e->name == "inverse") {
            const bool table = e->name == "table";
            const std::size_t header = table ? 2 : 3;
            for (std::size_t i = 0; i < header; ++i) {
                if (!fitsInt64(*e->args[i])) {
                    error(e->name + " shape requires constant machine-size integers", loc);
                    return false;
                }
            }
            const auto size = e->args[table ? 0 : 2]->int_value;
            if (size < 0 || static_cast<unsigned long long>(size) > e->args.size() - header) {
                error(e->name + " has an invalid tuple/vector size", loc);
                return false;
            }
            const std::size_t n = static_cast<std::size_t>(size);
            if (table) {
                const auto rows = e->args[1]->int_value;
                const std::size_t cells = e->args.size() - header - n;
                // Division before multiplication avoids overflowing a malicious shape.
                if (rows < 0 || (n == 0 ? cells != 0 :
                    (cells % n != 0 || static_cast<unsigned long long>(rows) != cells / n))) {
                    error("table dimensions disagree with its row-major cells", loc);
                    return false;
                }
                for (std::size_t i = header; i < e->args.size(); ++i) {
                    const auto& sort = e->args[i]->sort;
                    if ((sort.kind != SortKind::INT && sort.kind != SortKind::BOOL)
                        || !sameSort(sort, e->args[header + (i - header) % n]->sort)) {
                        error("table entries must match their Int or Bool tuple column", loc);
                        return false;
                    }
                }
            } else {
                for (std::size_t i = header; i < e->args.size(); ++i) {
                    if (e->args[i]->sort.kind != SortKind::INT) {
                        error("inverse requires Int vector elements", loc);
                        return false;
                    }
                }
            }
            if (e->sort.kind != SortKind::BOOL) {
                error(e->name + " must yield Bool", loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }
        if (e->name == "circuit") {
            for (const auto& arg : e->args) {
                if (arg->sort.kind != SortKind::INT) {
                    error("circuit requires an Int start and Int successors", loc);
                    return false;
                }
            }
            if (e->args.front()->kind != ExprKind::LIT_INT) {
                error("circuit's start index must be a constant integer", loc);
                return false;
            }
            if (e->sort.kind != SortKind::BOOL) {
                error("circuit must yield Bool", loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }
        if (e->name == "alldifferent" && !indexed) {
            // Every term numeric, and all of the same sort: `alldifferent(x, y)`
            // over an Int and a Real would decompose to comparisons that are
            // legal in SMT-LIB and are not what the model said.
            for (std::size_t i = 0; i < e->args.size(); ++i) {
                if (!isNumeric(e->args[i]->sort.kind)) {
                    error("alldifferent's argument " + std::to_string(i + 1) + " is "
                              + toString(e->args[i]->sort) + ", not numeric",
                          loc);
                    return false;
                }
                if (!sameSort(e->args[i]->sort, e->args[0]->sort)) {
                    error("alldifferent's arguments must all have the same sort; "
                          "argument " + std::to_string(i + 1) + " is "
                              + toString(e->args[i]->sort) + " and argument 1 is "
                              + toString(e->args[0]->sort),
                          loc);
                    return false;
                }
            }
            return true;
        }
        if (e->name == "alldifferent_except_0") {
            if (!indexed) {
                for (std::size_t i = 0; i < e->args.size(); ++i) {
                    if (e->args[i]->sort.kind != SortKind::INT) {
                        error("alldifferent_except_0's argument "
                                  + std::to_string(i + 1) + " is "
                                  + toString(e->args[i]->sort) + ", not Int",
                              loc);
                        return false;
                    }
                }
            } else {
                const Sort& array = e->args[0]->sort;
                if (!array.index || array.index->kind != SortKind::INT) {
                    error("alldifferent_except_0's array index sort must be Int",
                          loc);
                    return false;
                }
                if (!array.elem || array.elem->kind != SortKind::INT) {
                    error("alldifferent_except_0's array element sort must be Int",
                          loc);
                    return false;
                }
                for (std::size_t i = 1; i < 3; ++i) {
                    if (e->args[i]->sort.kind != SortKind::INT) {
                        error("alldifferent_except_0's "
                                  + std::string(i == 1 ? "lower" : "upper")
                                  + " index bound must be Int",
                              loc);
                        return false;
                    }
                }
            }
            if (e->sort.kind != SortKind::BOOL) {
                error("alldifferent_except_0 must yield Bool", loc,
                      ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }
        if (e->name == "alldifferent") {
            // Redundant while `indexed` IS "args[0] is an array" -- and kept,
            // because it is the check that stops being redundant the moment
            // someone dispatches the shape on the argument COUNT instead. That
            // change passes every behavioural test (decompose-globals makes its
            // own sort-based decision, so the encoding still comes out right)
            // and silently degrades the DIAGNOSTIC: `alldifferent(b1, b2, b3)`
            // over Booleans would be read as an indexed form and reported as
            // "alldifferent's lower index bound is Bool", naming an index bound
            // the author never wrote.
            if (e->args[0]->sort.kind != SortKind::ARRAY) {
                error("alldifferent's first argument must be an array, not "
                          + toString(e->args[0]->sort),
                      loc);
                return false;
            }
            for (std::size_t i = 1; i < 3; ++i) {
                if (!isNumeric(e->args[i]->sort.kind)) {
                    error(std::string("alldifferent's ")
                              + (i == 1 ? "lower" : "upper") + " index bound is "
                              + toString(e->args[i]->sort) + ", not numeric",
                          loc);
                    return false;
                }
            }
        }
        if (e->name == "count") {
            // The last two arguments are the sought value and the count; the
            // ones before them are the terms (list shape) or the array and its
            // bounds (indexed shape).
            const std::size_t n = e->args.size();
            const ExprPtr& sought = e->args[n - 2];
            const ExprPtr& howmany = e->args[n - 1];
            if (!isNumeric(howmany->sort.kind)) {
                error("count's occurrence count is " + toString(howmany->sort)
                          + ", not numeric",
                      loc);
                return false;
            }
            if (indexed) {
                for (std::size_t i = 1; i < 3; ++i) {
                    if (!isNumeric(e->args[i]->sort.kind)) {
                        error(std::string("count's ")
                                  + (i == 1 ? "lower" : "upper") + " index bound is "
                                  + toString(e->args[i]->sort) + ", not numeric",
                              loc);
                        return false;
                    }
                }
                if (!e->args[0]->sort.elem) {
                    error("count's array argument has no element sort", loc,
                          ErrorCode::E_INTERNAL);
                    return false;
                }
                const Sort elem = *e->args[0]->sort.elem;
                if (!sameSort(elem, sought->sort)) {
                    error("count looks for " + toString(sought->sort)
                              + " in an array of " + toString(elem),
                          loc);
                    return false;
                }
                return true;
            }
            // Every term must have the sought value's sort. A `count` over a
            // mix would decompose to equalities that are legal in SMT-LIB and
            // are not what the model said -- the same trap alldifferent's list
            // shape guards against one line up.
            for (std::size_t i = 0; i + 2 < n; ++i) {
                if (!sameSort(e->args[i]->sort, sought->sort)) {
                    error("count's term " + std::to_string(i + 1) + " is "
                              + toString(e->args[i]->sort)
                              + " and the value sought is " + toString(sought->sort),
                          loc);
                    return false;
                }
            }
            return true;
        }
        if (e->sort.kind != SortKind::BOOL) {
            error("a global constraint yields Bool, but the expression records "
                      + toString(e->sort),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    bool checkConnectivityGlobal(const ExprPtr& e, const SourceLoc& loc) {
        const auto fail = [&](const std::string& message) {
            error(e->name + ": " + message, loc, ErrorCode::E_TYPE);
            return false;
        };
        if (e->args.size() < 2) {
            return fail("expected literal node and edge counts N and E");
        }
        for (std::size_t i = 0; i < 2; ++i) {
            if (e->args[i]->sort.kind != SortKind::INT) {
                return fail(i == 0 ? "N must have exact Int sort"
                                   : "E must have exact Int sort");
            }
            if (e->args[i]->kind != ExprKind::LIT_INT || !fitsInt64(*e->args[i])) {
                return fail(i == 0 ? "N must be a representable Int literal"
                                   : "E must be a representable Int literal");
            }
            if (e->args[i]->int_value < 0) {
                return fail(i == 0 ? "N must be nonnegative" : "E must be nonnegative");
            }
        }
        const auto nodes = static_cast<unsigned long long>(e->args[0]->int_value);
        const auto edges = static_cast<unsigned long long>(e->args[1]->int_value);
        const auto max = static_cast<unsigned long long>(
            std::numeric_limits<std::size_t>::max());
        if (edges > (max - 2) / 3 || nodes > max - 2 - 3 * edges) {
            return fail("N and E exceed the representable argument count");
        }
        const std::size_t expected = static_cast<std::size_t>(2 + nodes + 3 * edges);
        if (e->args.size() != expected) {
            return fail("argument count does not match N and E (expected "
                        + std::to_string(expected) + ")");
        }
        const std::size_t endpoint_begin = 2;
        const std::size_t node_begin = endpoint_begin + 2 * static_cast<std::size_t>(edges);
        const std::size_t edge_begin = node_begin + static_cast<std::size_t>(nodes);
        for (std::size_t i = endpoint_begin; i < node_begin; ++i) {
            const auto& endpoint = e->args[i];
            if (endpoint->sort.kind != SortKind::INT) {
                return fail("edge endpoints must have exact Int sort");
            }
            if (endpoint->kind != ExprKind::LIT_INT || !fitsInt64(*endpoint)) {
                return fail("edge endpoints must be representable Int literals");
            }
            if (endpoint->int_value < 0
                || static_cast<unsigned long long>(endpoint->int_value) >= nodes) {
                return fail("edge endpoint is outside the zero-based node range [0,N)");
            }
        }
        for (std::size_t i = node_begin; i < edge_begin; ++i) {
            if (e->args[i]->sort.kind != SortKind::BOOL) {
                return fail("node selections must have exact Bool sort");
            }
        }
        for (std::size_t i = edge_begin; i < expected; ++i) {
            if (e->args[i]->sort.kind != SortKind::BOOL) {
                return fail("edge selections must have exact Bool sort");
            }
        }
        if (e->sort.kind != SortKind::BOOL) {
            error(e->name + " must yield Bool", loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    bool checkOp(const ExprPtr& e, const SourceLoc& loc) {
        if (e->op == Op::ARRAY_MAP_AND || e->op == Op::ARRAY_MAP_OR || e->op == Op::ARRAY_MAP_NOT) {
            if ((e->op == Op::ARRAY_MAP_NOT && e->args.size() != 1)
                || (e->op != Op::ARRAY_MAP_NOT && e->args.size() < 2)) {
                error("invalid Boolean array map arity", loc);
                return false;
            }
            for (const auto& arg : e->args) {
                if (!checkedOperand(arg, loc)) return false;
                const auto& sort = arg->sort;
                if (sort.kind != SortKind::ARRAY || !sort.index || !sort.elem
                    || sort.elem->kind != SortKind::BOOL || !sameSort(sort, e->sort)) {
                    error("Boolean array map needs arrays with identical index sorts and Bool elements", loc);
                    return false;
                }
            }
            return true;
        }
        if (e->op == Op::CONST_ARRAY) {
            // `((as const (Array T U)) v)`. The array sort is on the
            // EXPRESSION, not derivable from the argument -- v fixes U and says
            // nothing about T -- so the check runs the other way round: the
            // recorded sort must be an array, and v must have its element sort.
            if (e->args.size() != 1) {
                error("a constant array takes one value, not "
                          + std::to_string(e->args.size()) + " argument(s)", loc);
                return false;
            }
            if (e->sort.kind != SortKind::ARRAY || !e->sort.elem) {
                error("a constant array records sort " + toString(e->sort)
                          + ", which is not an array sort", loc, ErrorCode::E_INTERNAL);
                return false;
            }
            if (!sameSort(e->args[0]->sort, *e->sort.elem)) {
                error("the value of this constant array is "
                          + toString(e->args[0]->sort) + ", but the array holds "
                          + toString(*e->sort.elem),
                      locOf(e->args[0], loc));
                return false;
            }
            return true;
        }
        if (e->op == Op::SELECT) {
            if (e->args.size() != 2) {
                error("'select' takes an array and an index, not "
                          + std::to_string(e->args.size()) + " argument(s)", loc);
                return false;
            }
            if (!checkedOperand(e->args[0], loc) || !checkedOperand(e->args[1], loc)) {
                return false;
            }
            const Sort& arr = e->args[0]->sort;
            if (arr.kind != SortKind::ARRAY || !arr.index || !arr.elem) {
                error(std::string("'select' applied to ") + toString(arr)
                          + ", not an array",
                      loc);
                return false;
            }
            if (!sameSort(*arr.index, e->args[1]->sort)) {
                error(std::string("'select' index is ")
                          + toString(e->args[1]->sort)
                          + " but the array is indexed by "
                          + toString(*arr.index),
                      loc);
                return false;
            }
            if (!sameSort(*arr.elem, e->sort)) {
                error("'select' yields the array's element sort, but the "
                      "expression records a different one",
                      loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }

        if (e->op == Op::ITE) {
            if (e->args.size() != 3) {
                error("'ite' takes a condition and two branches, not "
                          + std::to_string(e->args.size()) + " argument(s)", loc);
                return false;
            }
            for (const auto& a : e->args) {
                if (!checkedOperand(a, loc)) { return false; }
            }
            if (e->args[0]->sort.kind != SortKind::BOOL) {
                error("'ite' condition is " + toString(e->args[0]->sort) + ", not Bool",
                      locOf(e->args[0], loc));
                return false;
            }
            if (!sameSort(e->args[1]->sort, e->args[2]->sort)) {
                error("'ite' branches are " + toString(e->args[1]->sort) + " and "
                          + toString(e->args[2]->sort) + "; they must agree",
                      locOf(e->args[2], loc));
                return false;
            }
            if (!sameSort(e->sort, e->args[1]->sort)) {
                error("'ite' yields its branches' sort, but the expression records "
                          + toString(e->sort), loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }

        if (isSetOp(e->op)) { return checkSetOp(e, loc); }
        if (isTupleOp(e->op)) { return checkTupleOp(e, loc); }

        if (e->op == Op::STORE) {
            if (e->args.size() != 3) {
                error("'store' takes an array, an index and a value, not "
                          + std::to_string(e->args.size()) + " argument(s)", loc);
                return false;
            }
            for (const auto& a : e->args) {
                if (!checkedOperand(a, loc)) { return false; }
            }
            const Sort& arr = e->args[0]->sort;
            if (arr.kind != SortKind::ARRAY || !arr.index || !arr.elem) {
                error("'store' applied to " + toString(arr) + ", not an array", loc);
                return false;
            }
            if (!sameSort(e->args[1]->sort, *arr.index)) {
                error("'store' index is " + toString(e->args[1]->sort)
                          + ", but the array is indexed by " + toString(*arr.index),
                      locOf(e->args[1], loc));
                return false;
            }
            // The value must match the ELEMENT sort. Checking it against the
            // index sort instead passes for (Array Int Int) and fails silently
            // for every other array, which is the shape of bug an
            // Int-indexed-Int-valued test cannot see.
            if (!sameSort(e->args[2]->sort, *arr.elem)) {
                error("'store' value is " + toString(e->args[2]->sort)
                          + ", but the array's elements are " + toString(*arr.elem),
                      locOf(e->args[2], loc));
                return false;
            }
            if (!sameSort(arr, e->sort)) {
                error("'store' yields the array's own sort, but the expression "
                      "records " + toString(e->sort), loc, ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }

        const char* name = opName(e->op);
        OpRule rule{};
        if (name == nullptr || !ruleFor(e->op, rule)) {
            error("an expression uses an operator this checker does not know",
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }

        bool args_ok = true;
        for (const auto& a : e->args) {
            if (!checkedOperand(a, loc)) { args_ok = false; }
        }
        if (!args_ok) { return false; }

        const std::size_t n = e->args.size();
        if (n < rule.min_args || (rule.max_args != 0 && n > rule.max_args)) {
            std::string want = std::to_string(rule.min_args);
            if (rule.max_args == 0) {
                want += " or more";
            } else if (rule.max_args != rule.min_args) {
                want += " to " + std::to_string(rule.max_args);
            }
            error(std::string("'") + name + "' takes " + want
                      + " argument(s), not " + std::to_string(n), loc);
            return false;
        }

        switch (rule.args) {
        case OpRule::Args::BOOL:
            for (std::size_t i = 0; i < n; ++i) {
                if (e->args[i]->sort.kind != SortKind::BOOL) {
                    error(std::string("argument ") + std::to_string(i + 1) + " of '"
                              + name + "' is " + toString(e->args[i]->sort)
                              + ", not Bool",
                          locOf(e->args[i], loc));
                    return false;
                }
            }
            break;
        case OpRule::Args::NUMERIC:
            for (std::size_t i = 0; i < n; ++i) {
                if (!isNumeric(e->args[i]->sort.kind)) {
                    error(std::string("argument ") + std::to_string(i + 1) + " of '"
                              + name + "' is " + toString(e->args[i]->sort)
                              + ", not numeric",
                          locOf(e->args[i], loc));
                    return false;
                }
            }
            break;
        case OpRule::Args::SAME_ANY: {
            const Sort& first = e->args[0]->sort;
            for (std::size_t i = 1; i < n; ++i) {
                const Sort& k = e->args[i]->sort;
                // sameSort, not kind equality. Comparing kinds alone made
                // (= x y) type-check for an 8-bit x and a 32-bit y, because
                // both are BITVEC -- and nothing downstream re-checks, so the
                // mismatch would have reached the solver as a malformed term.
                // Int and Real still compare with each other; everything else
                // must match structurally, widths and sort names included.
                const bool compatible = sameSort(k, first)
                    || (isNumeric(k.kind) && isNumeric(first.kind));
                if (!compatible) {
                    // No width/name suffix any more: toString prints the whole
                    // sort, so "(_ BitVec 8) with (_ BitVec 32)" already says
                    // what the suffix used to have to add back.
                    error(std::string("'") + name + "' compares "
                              + toString(first) + " with " + toString(k),
                          locOf(e->args[i], loc));
                    return false;
                }
            }
            break;
        }
        case OpRule::Args::BITVEC_SAME:
        case OpRule::Args::BITVEC_ANY: {
            for (std::size_t i = 0; i < n; ++i) {
                if (e->args[i]->sort.kind != SortKind::BITVEC) {
                    error(std::string("argument ") + std::to_string(i + 1) + " of '"
                              + name + "' is " + toString(e->args[i]->sort)
                              + ", not a bit-vector",
                          locOf(e->args[i], loc));
                    return false;
                }
                if (e->args[i]->sort.width == 0) {
                    error(std::string("argument ") + std::to_string(i + 1) + " of '"
                              + name + "' has width 0, which is not a sort",
                          locOf(e->args[i], loc), ErrorCode::E_INTERNAL);
                    return false;
                }
            }
            if (rule.args == OpRule::Args::BITVEC_SAME) {
                // The rule the whole widened SortKind exists to make checkable.
                // SMT-LIB requires equal widths here even for the shifts, where
                // it is tempting to pass a narrower distance.
                const Sort& first = e->args[0]->sort;
                for (std::size_t i = 1; i < n; ++i) {
                    if (!sameSort(e->args[i]->sort, first)) {
                        error(std::string("'") + name + "' needs its arguments at one "
                                  "width, but argument 1 is " + toString(first)
                                  + " and argument " + std::to_string(i + 1) + " is "
                                  + toString(e->args[i]->sort),
                              locOf(e->args[i], loc));
                        return false;
                    }
                }
            }
            break;
        }
        case OpRule::Args::SIGNATURE: {
            std::vector<SortKind> sig;
            bool variadic = false;
            if (!signatureFor(e->op, sig, variadic) || sig.empty()) {
                error("an expression uses an operator whose argument signature "
                      "this checker does not know",
                      loc, ErrorCode::E_INTERNAL);
                return false;
            }
            for (std::size_t i = 0; i < n; ++i) {
                // to_fp's source may be Real, Float or BitVec; the INDEXED
                // result branch checks that position, so the fixed signature
                // has nothing useful to say about it.
                if ((e->op == Op::TO_FP || e->op == Op::TO_FP_UNSIGNED) && i == 1) {
                    continue;
                }
                const SortKind want =
                    i < sig.size() ? sig[i]
                                   : (variadic ? sig.back() : sig.back());
                if (e->args[i]->sort.kind != want) {
                    error(std::string("argument ") + std::to_string(i + 1) + " of '"
                              + name + "' is " + toString(e->args[i]->sort)
                              + ", not " + sortName(want),
                          locOf(e->args[i], loc));
                    return false;
                }
            }
            // Every Float argument must be the SAME float sort. SMT-LIB requires
            // it, and the sorts are structural, so a single-precision and a
            // double-precision operand agree on kind and differ on everything
            // that matters -- the bit-vector width mistake in another theory.
            const Sort* first_float = nullptr;
            for (std::size_t i = 0; i < n; ++i) {
                if (e->args[i]->sort.kind != SortKind::FLOAT) { continue; }
                if (first_float == nullptr) {
                    first_float = &e->args[i]->sort;
                    continue;
                }
                if (!sameSort(e->args[i]->sort, *first_float)) {
                    error(std::string("'") + name + "' needs its floating-point "
                              "arguments at one format, but got " + toString(*first_float)
                              + " and " + toString(e->args[i]->sort),
                          locOf(e->args[i], loc));
                    return false;
                }
            }
            break;
        }
        }

        if (e->indices.size() != rule.index_count) {
            error(std::string("'") + name + "' takes "
                      + std::to_string(rule.index_count) + " index/indices, not "
                      + std::to_string(e->indices.size()),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }

        Sort expected;
        switch (rule.result) {
        case OpRule::Result::BOOL:
            expected = Sort::boolean();
            break;
        case OpRule::Result::WIDENED:
            expected = Sort{widened(e->args)};
            break;
        case OpRule::Result::ARG0:
            expected = e->args[0]->sort;
            break;
        case OpRule::Result::ARG1:
            // Guarded by the arity check above: every ARG1 rule has min_args 2.
            expected = e->args[1]->sort;
            break;
        case OpRule::Result::INT_RESULT:
            expected = Sort::integer();
            break;
        case OpRule::Result::STRING_RESULT:
            expected = Sort::string();
            break;
        case OpRule::Result::REAL_RESULT:
            expected = Sort::real();
            break;
        case OpRule::Result::REGLAN_RESULT:
            expected = Sort::regLan();
            break;
        case OpRule::Result::CONCAT_WIDTH: {
            unsigned total = 0;
            for (const auto& a : e->args) { total += a->sort.width; }
            expected = Sort::bitvec(total);
            break;
        }
        case OpRule::Result::INDEXED: {
            const unsigned w = e->args[0]->sort.width;
            if (e->op == Op::INT_TO_BV) {
                expected = Sort::bitvec(e->indices[0]);
                break;
            }
            if (e->op == Op::FP_TO_IEEE_BV) {
                // The bit pattern is exactly as wide as the format: sign, the
                // exponent field, and the significand minus its hidden bit.
                expected = Sort::bitvec(e->args[0]->sort.exponent_bits
                                        + e->args[0]->sort.significand_bits);
                break;
            }
            if (e->op == Op::FP_TO_SBV || e->op == Op::FP_TO_UBV) {
                expected = Sort::bitvec(e->indices[0]);
                break;
            }
            if (e->op == Op::TO_FP || e->op == Op::TO_FP_UNSIGNED) {
                // The source may be Real, Float or BitVec -- three different
                // conversions sharing one spelling in SMT-LIB -- so it is
                // checked here rather than by a fixed signature kind.
                const SortKind from = e->args[1]->sort.kind;
                const bool ok = from == SortKind::REAL || from == SortKind::FLOAT
                             || from == SortKind::BITVEC;
                if (!ok) {
                    error(std::string("'") + name + "' converts from Real, "
                              "FloatingPoint or a bit-vector, not "
                              + toString(e->args[1]->sort),
                          locOf(e->args[1], loc));
                    return false;
                }
                if (e->op == Op::TO_FP_UNSIGNED && from != SortKind::BITVEC) {
                    // to_fp_unsigned reads its argument as an unsigned
                    // bit-vector; there is nothing unsigned about a Real.
                    error("'to_fp_unsigned' converts from a bit-vector, not "
                              + toString(e->args[1]->sort),
                          locOf(e->args[1], loc));
                    return false;
                }
                expected = Sort::floating(e->indices[0], e->indices[1]);
                break;
            }
            if (e->op == Op::IEEE_BV_TO_FP) {
                // The bit pattern is exactly as wide as the format it
                // reinterprets: sign, exponent field, significand minus its
                // hidden bit -- the same arithmetic as FP_TO_IEEE_BV above,
                // in the other direction.
                if (e->args[0]->sort.width != e->indices[0] + e->indices[1]) {
                    error(std::string("'") + name + "' needs a bit-vector of width "
                              + std::to_string(e->indices[0] + e->indices[1])
                              + " (the format's full width), not "
                              + toString(e->args[0]->sort),
                          locOf(e->args[0], loc));
                    return false;
                }
                expected = Sort::floating(e->indices[0], e->indices[1]);
                break;
            }
            if (e->op == Op::BV_EXTRACT) {
                const unsigned hi = e->indices[0], lo = e->indices[1];
                // Both bounds matter and both are easy to get backwards. An
                // out-of-range extract is not a narrower result, it is a term
                // with no meaning; SMT-LIB requires w > hi >= lo >= 0.
                if (hi < lo) {
                    error(std::string("'extract' has hi < lo (") + std::to_string(hi)
                              + " < " + std::to_string(lo) + ")", loc);
                    return false;
                }
                if (hi >= w) {
                    error(std::string("'extract' reads bit ") + std::to_string(hi)
                              + " of " + toString(e->args[0]->sort), loc);
                    return false;
                }
                expected = Sort::bitvec(hi - lo + 1);
            } else if (e->op == Op::BV_ROTATE_LEFT
                       || e->op == Op::BV_ROTATE_RIGHT) {
                // A rotation moves bits; it neither adds nor drops any. Sharing
                // the extensions' `w + n` below would make every rotation
                // widen, which type-checks against nothing downstream and would
                // be reported as a mismatch three operators away.
                expected = e->args[0]->sort;
            } else if (e->op == Op::BV_REPEAT) {
                const unsigned times = e->indices[0];
                if (times == 0) {
                    // Width 0 is not a bit-vector sort. SMT-LIB requires n >= 1.
                    error("'repeat' needs at least one repetition", loc);
                    return false;
                }
                expected = Sort::bitvec(w * times);
            } else {
                expected = Sort::bitvec(w + e->indices[0]);
            }
            break;
        }
        case OpRule::Result::BITVEC_ONE:
            expected = Sort::bitvec(1);
            break;
        }
        if (!sameSort(e->sort, expected)) {
            // mkOp() derives this, so a mismatch means the expression was built
            // by hand with the wrong sort recorded -- and every consumer,
            // including this checker's own parent frame, trusts the recorded
            // sort over re-deriving it.
            error(std::string("'") + name + "' yields " + toString(expected)
                      + " here, but the expression records " + toString(e->sort),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    /** Validate nominal datatype references wherever they occur in a sort.
     *
     *  Datatype-valued fields commonly put the datatype under Array, Set, or a
     *  parametric datatype application. Checking only the outer SortKind
     *  misses unknown names and wrong arities until lowerSort, after the model
     *  has already passed type checking. Type parameters are represented as
     *  zero-arity UNINTERPRETED sorts and shadow global sort names only within
     *  their owning declaration. */
    bool checkDatatypeSortReferences(const Sort& root,
                                     const std::vector<std::string>& params,
                                     const SourceLoc& loc,
                                     const std::string& where) {
        bool valid = true;
        struct Frame { const Sort* sort; bool done; };
        std::vector<Frame> pending{{&root, false}};
        std::unordered_set<const Sort*> active, visited;
        while (!pending.empty()) {
            const auto frame = pending.back();
            pending.pop_back();
            if (!frame.sort) {
                error(where + " contains a null sort argument", loc, ErrorCode::E_INTERNAL);
                valid = false;
                continue;
            }
            if (frame.done) {
                active.erase(frame.sort);
                visited.insert(frame.sort);
                continue;
            }
            if (visited.count(frame.sort)) { continue; }
            if (!active.insert(frame.sort).second) {
                error(where + " contains a cyclic structural sort", loc, ErrorCode::E_INTERNAL);
                valid = false;
                continue;
            }
            const auto& sort = *frame.sort;
            if (sort.kind == SortKind::DATATYPE) {
                const auto it = datatypes_.find(sort.name);
                if (it == datatypes_.end()) {
                    error(where + " references undeclared datatype '" + sort.name + "'", loc);
                    valid = false;
                } else if (sort.args.size() != it->second->params.size()) {
                    error(where + " applies datatype '" + sort.name + "' to "
                              + std::to_string(sort.args.size()) + " sort argument(s), but its arity is "
                              + std::to_string(it->second->params.size()), loc);
                    valid = false;
                }
            }
            if (sort.kind == SortKind::UNINTERPRETED
                && std::find(params.begin(), params.end(), sort.name) != params.end()
                && !sort.args.empty()) {
                error(where + " applies sort parameter '" + sort.name
                          + "' as a sort constructor", loc);
                valid = false;
            }
            if (sort.kind == SortKind::UNINTERPRETED
                && std::find(params.begin(), params.end(), sort.name) == params.end()) {
                const auto declaration = uninterpreted_sorts_.find(sort.name);
                if (declaration != uninterpreted_sorts_.end()
                    && sort.args.size() != declaration->second) {
                    error(where + " applies sort constructor '" + sort.name + "' to "
                              + std::to_string(sort.args.size())
                              + " sort argument(s), but its arity is "
                              + std::to_string(declaration->second), loc);
                    valid = false;
                }
            }
            pending.push_back({&sort, true});
            for (auto it = sort.args.rbegin(); it != sort.args.rend(); ++it) {
                pending.push_back({it->get(), false});
            }
            if (sort.elem) { pending.push_back({sort.elem.get(), false}); }
            if (sort.index) { pending.push_back({sort.index.get(), false}); }
        }
        return valid;
    }

    /** Every datatype declaration, and the flattened constructor and selector
     *  tables built from them. SMT-LIB requires constructor and selector names
     *  to be unique across ALL datatypes in scope, not merely within one, so
     *  one table each is the shape the rule wants. */
    void checkDatatypes() {
        for (const auto& dt : model_.datatypes) {
            if (dt.name.empty()) {
                error("a datatype has no name", dt.loc, ErrorCode::E_INTERNAL);
                continue;
            }
            if (!datatypes_.emplace(dt.name, &dt).second) {
                error("datatype '" + dt.name + "' is declared more than once", dt.loc);
                continue;
            }
            if (uninterpreted_sorts_.count(dt.name) != 0) {
                error("sort constructor '" + dt.name
                          + "' is declared both as an uninterpreted sort and a datatype",
                      dt.loc);
            }
            if (dt.constructors.empty()) {
                // A datatype with no constructors has no values, so every
                // variable of it makes the model unsatisfiable -- an answer,
                // not a translation.
                error("datatype '" + dt.name + "' has no constructors", dt.loc);
            }
        }
        // Registered in a second pass so a selector may name a datatype
        // declared later in the list: mutual recursion between two datatypes is
        // ordinary modelling, and rejecting a forward reference would refuse it.
        for (const auto& dt : model_.datatypes) {
            for (const auto& ctor : dt.constructors) {
                if (!constructors_.emplace(ctor.name, std::make_pair(&dt, &ctor)).second) {
                    error("constructor '" + ctor.name + "' is declared more than "
                          "once; SMT-LIB requires constructor names to be unique "
                          "across all datatypes in scope", dt.loc);
                }
                for (const auto& sel : ctor.selectors) {
                    if (!selectors_.emplace(sel.name, std::make_pair(&dt, &sel)).second) {
                        error("selector '" + sel.name + "' is declared more than once",
                              dt.loc);
                    }
                }
            }
        }
        // Sort references need the full registry above, including forward and
        // mutually recursive references. Walk container components and applied
        // sort arguments as well as a field's outer sort.
        for (const auto& dt : model_.datatypes) {
            for (const auto& ctor : dt.constructors) {
                for (const auto& sel : ctor.selectors) {
                    checkDatatypeSortReferences(sel.sort, dt.params, dt.loc,
                                                "selector '" + sel.name + "'");
                }
            }
        }
        // A declaration block has one fixed-point interpretation. Different
        // blocks may depend on each other, but a recursive SCC cannot mix
        // least and greatest fixed points in the target syntax.
        std::unordered_map<std::string, std::unordered_set<std::string>> dependencies;
        for (const auto& dt : model_.datatypes) {
            if (!datatypes_.count(dt.name)) { continue; }
            const auto collect = [&](const Sort& root) {
                std::vector<const Sort*> pending{&root};
                std::unordered_set<const Sort*> visited;
                while (!pending.empty()) {
                    const auto& sort = *pending.back();
                    pending.pop_back();
                    if (!visited.insert(&sort).second) { continue; }
                    // Type parameters shadow global sort names in this declaration.
                    bool parameter = false;
                    for (const auto& name : dt.params) { parameter |= name == sort.name; }
                    if (sort.kind == SortKind::UNINTERPRETED && parameter) { continue; }
                    if (datatypes_.count(sort.name)) { dependencies[dt.name].insert(sort.name); }
                    if (sort.index) { pending.push_back(sort.index.get()); }
                    if (sort.elem) { pending.push_back(sort.elem.get()); }
                    for (const auto& argument : sort.args) { if (argument) { pending.push_back(argument.get()); } }
                }
            };
            for (const auto& constructor : dt.constructors) {
                for (const auto& selector : constructor.selectors) { collect(selector.sort); }
            }
        }
        const auto reachable = [&](const std::string& start) {
            std::unordered_set<std::string> seen;
            std::vector<std::string> work{start};
            while (!work.empty()) {
                const auto at = work.back();
                work.pop_back();
                if (!seen.insert(at).second) { continue; }
                const auto edges = dependencies.find(at);
                if (edges != dependencies.end()) {
                    work.insert(work.end(), edges->second.begin(), edges->second.end());
                }
            }
            return seen;
        };
        for (const auto& dt : model_.datatypes) {
            if (!datatypes_.count(dt.name)) { continue; }
            for (const auto& name : reachable(dt.name)) {
                if (datatypes_.at(name)->coinductive != dt.coinductive
                    && reachable(name).count(dt.name)) {
                    error("mutually recursive datatype group mixes inductive and coinductive declarations",
                          dt.loc);
                    break;
                }
            }
        }
    }

    /** Bind a parametric datatype's parameters from an instance of it.
     *
     *  A member of a parametric datatype is polymorphic and the declaration
     *  records the parameters rather than an instance: `hd : X`. The instance is
     *  the argument, and its sort arguments are the parameters in order. */
    static std::unordered_map<std::string, Sort> dtBinding(const DatatypeDecl& owner,
                                                          const Sort& instance) {
        std::unordered_map<std::string, Sort> b;
        for (std::size_t i = 0; i < owner.params.size() && i < instance.args.size(); ++i) {
            if (instance.args[i]) { b[owner.params[i]] = *instance.args[i]; }
        }
        return b;
    }

    /** Replace every parameter in @p s by its binding, at any depth. */
    static Sort dtSubstitute(const Sort& s,
                             const std::unordered_map<std::string, Sort>& b) {
        if (b.empty()) { return s; }
        Sort out = s;
        struct Frame { const Sort* source; Sort* target; };
        std::vector<Frame> pending{{&s, &out}};
        std::unordered_map<const Sort*, std::shared_ptr<Sort>> copied;
        const auto clone = [&](const std::shared_ptr<const Sort>& source) {
            if (!source) { return std::shared_ptr<Sort>{}; }
            const auto found = copied.find(source.get());
            if (found != copied.end()) { return found->second; }
            auto target = std::make_shared<Sort>(*source);
            copied.emplace(source.get(), target);
            pending.push_back({source.get(), target.get()});
            return target;
        };
        while (!pending.empty()) {
            const auto frame = pending.back();
            pending.pop_back();
            const auto& source = *frame.source;
            // Only a nullary uninterpreted leaf is a lexical type parameter.
            if (source.kind == SortKind::UNINTERPRETED && source.args.empty()
                && !source.name.empty()) {
                const auto binding = b.find(source.name);
                if (binding != b.end()) { *frame.target = binding->second; continue; }
            }
            frame.target->index = clone(source.index);
            frame.target->elem = clone(source.elem);
            frame.target->args.clear();
            frame.target->args.reserve(source.args.size());
            for (const auto& argument : source.args) { frame.target->args.push_back(clone(argument)); }
        }
        return out;
    }

    bool checkDtValue(const ExprPtr& e, const DatatypeDecl& owner,
                      const char* what, const SourceLoc& loc) {
        if (!checkedOperand(e->args[0], loc)) { return false; }
        // A PARAMETRIC datatype's member applies to an INSTANCE, so the expected
        // sort carries the argument's own arguments: `hd` of an `(L Int)` is
        // applied to `(L Int)` and not to the unapplied `L`. Comparing against
        // the bare name reported "applied to (L Int), not L" for a term that is
        // exactly right.
        Sort want = owner.params.empty()
            ? Sort::datatype(owner.name)
            : e->args[0]->sort;
        if (!owner.params.empty()
            && (want.kind != SortKind::DATATYPE || want.name != owner.name
                || want.args.size() != owner.params.size())) {
            want = Sort::datatype(owner.name);
        }
        if (!sameSort(e->args[0]->sort, want)) {
            error(std::string(what) + " '" + e->name + "' applied to "
                      + toString(e->args[0]->sort) + ", not " + toString(want),
                  locOf(e->args[0], loc));
            return false;
        }
        return true;
    }

    /** The tuple operators.
     *
     *  Every one of them relates an INDEX to a position in a heterogeneous
     *  sort, so there is nothing for the uniform rule table to say: the check
     *  that matters is that each index is inside the tuple's arity, and that
     *  is also the check the engine's own builders make before they will build
     *  the node at all. Letting an out-of-range index through here would reach
     *  `Parser::mkTupleSelect`, which reports through a different channel and
     *  yields an unknown node -- a type error surfacing as a lowering failure
     *  with no source location. */
    bool checkTupleOp(const ExprPtr& e, const SourceLoc& loc) {
        const char* name = opName(e->op);
        for (const auto& a : e->args) {
            if (!checkedOperand(a, loc)) { return false; }
        }
        // The constructor is the one that takes no index: its sort IS its
        // arguments' sorts, in order.
        if (e->op == Op::TUPLE) {
            if (e->args.empty()) {
                error("'tuple' takes at least one field; the nullary tuple is "
                      "the constant tuple.unit", loc);
                return false;
            }
            if (!e->indices.empty()) {
                error("'tuple' is not an indexed operator", loc,
                      ErrorCode::E_INTERNAL);
                return false;
            }
            std::vector<Sort> fields;
            fields.reserve(e->args.size());
            for (const auto& a : e->args) { fields.push_back(a->sort); }
            const Sort expected = Sort::tuple(std::move(fields));
            if (!sameSort(e->sort, expected)) {
                error("'tuple' yields " + toString(expected) + " here, but the "
                      "expression records " + toString(e->sort), loc,
                      ErrorCode::E_INTERNAL);
                return false;
            }
            return true;
        }
        const std::size_t want_args = (e->op == Op::TUPLE_UPDATE) ? 2 : 1;
        if (e->args.size() != want_args) {
            error(std::string("'") + name + "' takes "
                      + std::to_string(want_args) + " argument(s), not "
                      + std::to_string(e->args.size()), loc);
            return false;
        }
        const Sort& t = e->args[0]->sort;
        if (t.kind != SortKind::TUPLE) {
            error(std::string("argument 1 of '") + name + "' is " + toString(t)
                      + ", not a tuple", locOf(e->args[0], loc));
            return false;
        }
        // tuple.select and tuple.update take exactly one index; tuple.project
        // takes any number, INCLUDING none -- the projection onto no fields is
        // UnitTuple, which is a value and not an error.
        if (e->op != Op::TUPLE_PROJECT && e->indices.size() != 1) {
            error(std::string("'") + name + "' takes one index, not "
                      + std::to_string(e->indices.size()), loc,
                  ErrorCode::E_INTERNAL);
            return false;
        }
        for (unsigned i : e->indices) {
            if (i >= t.args.size()) {
                error(std::string("'") + name + "' selects field "
                          + std::to_string(i) + " of " + toString(t)
                          + ", which has " + std::to_string(t.args.size())
                          + " field(s)", loc);
                return false;
            }
            if (!t.args[i]) {
                error(std::string("'") + name + "' is applied to a malformed "
                      "tuple sort", loc, ErrorCode::E_INTERNAL);
                return false;
            }
        }
        Sort expected;
        switch (e->op) {
        case Op::TUPLE_SELECT:
            expected = *t.args[e->indices[0]];
            break;
        case Op::TUPLE_UPDATE:
            // The new value must have the sort of the field it replaces --
            // this is the whole content of the check, and without it an update
            // could silently change a tuple's sort while still recording the
            // old one.
            if (!sameSort(e->args[1]->sort, *t.args[e->indices[0]])) {
                error("'tuple.update' replaces field "
                          + std::to_string(e->indices[0]) + " of " + toString(t)
                          + " with " + toString(e->args[1]->sort),
                      locOf(e->args[1], loc));
                return false;
            }
            expected = t;
            break;
        default: {
            std::vector<Sort> fields;
            fields.reserve(e->indices.size());
            for (unsigned i : e->indices) { fields.push_back(*t.args[i]); }
            expected = Sort::tuple(std::move(fields));
            break;
        }
        }
        if (!sameSort(e->sort, expected)) {
            error(std::string("'") + name + "' yields " + toString(expected)
                      + " here, but the expression records " + toString(e->sort),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    /** The finite-set operators. Their shapes relate a container to its element
     *  sort, which no uniform "all arguments the same" rule describes, and two
     *  of them read backwards from their names: set.member takes the element
     *  first, set.insert takes the set last. */
    bool checkSetOp(const ExprPtr& e, const SourceLoc& loc) {
        const char* name = opName(e->op);
        for (const auto& a : e->args) {
            if (!checkedOperand(a, loc)) { return false; }
        }
        const auto arity = [&](std::size_t lo, std::size_t hi) {
            if (e->args.size() >= lo && (hi == 0 || e->args.size() <= hi)) { return true; }
            error(std::string("'") + name + "' takes " + std::to_string(lo)
                      + (hi == lo ? "" : hi == 0 ? " or more" : "-" + std::to_string(hi))
                      + " argument(s), not " + std::to_string(e->args.size()), loc);
            return false;
        };
        const auto isSet = [&](std::size_t i) {
            if (e->args[i]->sort.kind == SortKind::SET && e->args[i]->sort.elem) {
                return true;
            }
            error(std::string("argument ") + std::to_string(i + 1) + " of '" + name
                      + "' is " + toString(e->args[i]->sort) + ", not a set",
                  locOf(e->args[i], loc));
            return false;
        };
        Sort expected;
        switch (e->op) {
        case Op::SET_SINGLETON:
            if (!arity(1, 1)) { return false; }
            expected = Sort::set(e->args[0]->sort);
            break;
        case Op::SET_CARD:
            if (!arity(1, 1) || !isSet(0)) { return false; }
            expected = Sort::integer();
            break;
        case Op::SET_COMPLEMENT:
            if (!arity(1, 1) || !isSet(0)) { return false; }
            expected = e->args[0]->sort;
            break;
        case Op::SET_MEMBER: {
            if (!arity(2, 2) || !isSet(1)) { return false; }
            // The element is FIRST. Accepting either order would make the two
            // spellings mean the same thing, and only one of them is SMT-LIB.
            if (!sameSort(e->args[0]->sort, *e->args[1]->sort.elem)) {
                error("'set.member' relates " + toString(e->args[0]->sort)
                          + " to " + toString(e->args[1]->sort),
                      locOf(e->args[0], loc));
                return false;
            }
            expected = Sort::boolean();
            break;
        }
        case Op::SET_SUBSET:
        case Op::SET_MINUS:
        case Op::SET_UNION:
        case Op::SET_INTER: {
            const std::size_t lo = (e->op == Op::SET_UNION || e->op == Op::SET_INTER) ? 1 : 2;
            const std::size_t hi = lo == 1 ? 0 : 2;
            if (!arity(lo, hi)) { return false; }
            for (std::size_t i = 0; i < e->args.size(); ++i) {
                if (!isSet(i)) { return false; }
                if (!sameSort(e->args[i]->sort, e->args[0]->sort)) {
                    error(std::string("'") + name + "' needs sets of one element "
                              "sort, but got " + toString(e->args[0]->sort)
                              + " and " + toString(e->args[i]->sort),
                          locOf(e->args[i], loc));
                    return false;
                }
            }
            expected = (e->op == Op::SET_SUBSET) ? Sort::boolean() : e->args[0]->sort;
            break;
        }
        case Op::SET_INSERT: {
            if (!arity(2, 0) || !isSet(e->args.size() - 1)) { return false; }
            const Sort& elem = *e->args.back()->sort.elem;
            for (std::size_t i = 0; i + 1 < e->args.size(); ++i) {
                if (!sameSort(e->args[i]->sort, elem)) {
                    error("element " + std::to_string(i + 1) + " of 'set.insert' is "
                              + toString(e->args[i]->sort) + ", but the set holds "
                              + toString(elem),
                          locOf(e->args[i], loc));
                    return false;
                }
            }
            expected = e->args.back()->sort;
            break;
        }
        default:
            error("an expression uses a set operator this checker does not know",
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        if (!sameSort(e->sort, expected)) {
            error(std::string("'") + name + "' yields " + toString(expected)
                      + " here, but the expression records " + toString(e->sort),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    bool checkDtConstructor(const ExprPtr& e, const SourceLoc& loc) {
        const auto it = constructors_.find(e->name);
        if (it == constructors_.end()) {
            error("application of undeclared constructor '" + e->name + "'", loc);
            return false;
        }
        const DatatypeDecl& dt = *it->second.first;
        const DtConstructor& ctor = *it->second.second;
        if (e->args.size() != ctor.selectors.size()) {
            error("constructor '" + e->name + "' takes "
                      + std::to_string(ctor.selectors.size()) + " field(s), not "
                      + std::to_string(e->args.size()), loc);
            return false;
        }
        // The recorded sort must be an INSTANCE of the declared datatype: a
        // parametric constructor yields `(Event Real)`, not the bare `Event`
        // its declaration names -- which is what the frontend's
        // `(as Absent (Event Real))` records. The instance then substitutes
        // the declaration's parameters for the field check, exactly as a
        // selector's result already does. For an ordinary datatype the
        // parameter list is empty and this reduces to the bare-name compare.
        if (e->sort.kind != SortKind::DATATYPE || e->sort.name != dt.name
            || e->sort.args.size() != dt.params.size()) {
            error("constructor '" + e->name + "' yields " + dt.name
                      + (dt.params.empty() ? std::string()
                                           : std::string(" applied to its parameter(s)"))
                      + ", but the expression records " + toString(e->sort),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        // Preserve the internal-invariant diagnosis for a constructor whose
        // recorded outer instance disagrees with its declaration. Only after
        // that check validate nominal references nested inside its arguments.
        if (!checkDatatypeSortReferences(e->sort, {}, loc,
                                         "result sort of constructor '" + e->name + "'")) {
            return false;
        }
        const std::unordered_map<std::string, Sort> dt_binding = dtBinding(dt, e->sort);
        for (std::size_t i = 0; i < e->args.size(); ++i) {
            if (!checkedOperand(e->args[i], loc)) { return false; }
            const Sort want = dtSubstitute(ctor.selectors[i].sort, dt_binding);
            if (!sameSort(e->args[i]->sort, want)) {
                error("field " + std::to_string(i + 1) + " of '" + e->name + "' is "
                          + toString(e->args[i]->sort) + ", but '"
                          + ctor.selectors[i].name + "' is "
                          + toString(want),
                      locOf(e->args[i], loc));
                return false;
            }
        }
        return true;
    }

    bool checkDtSelector(const ExprPtr& e, const SourceLoc& loc) {
        const auto it = selectors_.find(e->name);
        if (it == selectors_.end()) {
            error("application of undeclared selector '" + e->name + "'", loc);
            return false;
        }
        if (e->args.size() != 1) {
            error("selector '" + e->name + "' takes one argument, not "
                      + std::to_string(e->args.size()), loc);
            return false;
        }
        if (!checkDtValue(e, *it->second.first, "selector", loc)) { return false; }
        // The declared result may mention the datatype's parameters, so it is
        // compared after substituting them from the instance being selected
        // from. `hd : X` on an `(L Int)` yields Int.
        const Sort want = dtSubstitute(
            it->second.second->sort,
            dtBinding(*it->second.first, e->args[0]->sort));
        if (!sameSort(e->sort, want)) {
            error("selector '" + e->name + "' yields " + toString(want)
                      + ", but the expression records " + toString(e->sort),
                  loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    bool checkDtTester(const ExprPtr& e, const SourceLoc& loc) {
        const auto it = constructors_.find(e->name);
        if (it == constructors_.end()) {
            error("tester for undeclared constructor '" + e->name + "'", loc);
            return false;
        }
        if (e->args.size() != 1) {
            error("a tester takes one argument, not "
                      + std::to_string(e->args.size()), loc);
            return false;
        }
        if (!checkDtValue(e, *it->second.first, "tester for", loc)) { return false; }
        if (e->sort.kind != SortKind::BOOL) {
            error("a tester yields Bool, but the expression records "
                      + toString(e->sort), loc, ErrorCode::E_INTERNAL);
            return false;
        }
        return true;
    }

    const ConstraintModel& model_;
    Diagnostics&           diags_;
    ScalarRangeIndex       scalar_ranges_;
    // Checker borrows a const model for one synchronous typeCheck call. Names
    // and full sorts stay in its stable declaration vector; duplicating them
    // here costs a second large signature on million-column models.
    std::unordered_map<std::string_view, const Sort*> declared_;
    std::unordered_map<std::string, const FunDecl*> functions_;
    std::unordered_map<std::string, const DatatypeDecl*> datatypes_;
    std::unordered_map<std::string, std::size_t> uninterpreted_sorts_;
    std::unordered_map<std::string,
                       std::pair<const DatatypeDecl*, const DtConstructor*>> constructors_;
    std::unordered_map<std::string,
                       std::pair<const DatatypeDecl*, const DtSelector*>> selectors_;
    /** In scope from enclosing quantifiers, innermost last. */
    std::unordered_map<std::string, Sort> bound_;
    struct ExprCacheKey {
        const Expr* expression;
        std::size_t scope_epoch;
        bool operator==(const ExprCacheKey& other) const noexcept {
            return expression == other.expression && scope_epoch == other.scope_epoch;
        }
    };
    struct ExprCacheHash {
        std::size_t operator()(const ExprCacheKey& key) const noexcept {
            return std::hash<const Expr*>{}(key.expression)
                ^ (std::hash<std::size_t>{}(key.scope_epoch) << 1);
        }
    };
    std::unordered_set<ExprCacheKey, ExprCacheHash> check_cache_;
    std::size_t expr_depth_ = 0;
    std::size_t scope_epoch_ = 0;
    std::size_t next_scope_epoch_ = 0;
    bool retain_root_cache_ = false;
    bool                   ok_ = true;
};

} // namespace

const char* sortName(SortKind k) {
    switch (k) {
    case SortKind::BOOL: return "Bool";
    case SortKind::INT:  return "Int";
    case SortKind::REAL: return "Real";
    case SortKind::ARRAY: return "Array";
    case SortKind::BITVEC: return "BitVec";
    case SortKind::FLOAT: return "FloatingPoint";
    case SortKind::STRING: return "String";
    case SortKind::UNINTERPRETED: return "an uninterpreted sort";
    case SortKind::ROUNDING_MODE: return "RoundingMode";
    case SortKind::REGLAN: return "RegLan";
    case SortKind::DATATYPE: return "a datatype";
    case SortKind::SET: return "Set";
    case SortKind::TUPLE: return "Tuple";
    }
    // A new SortKind must fail here rather than print "?" inside the message
    // that is supposed to explain which sorts did not match.
    condAssert(false, "sortName: unhandled SortKind");
    return "";   // unreachable; condAssert always throws
}

bool typeCheck(const ConstraintModel& model, Diagnostics& diagnostics) {
    return Checker(model, diagnostics).run();
}

bool typeCheckTerms(const ConstraintModel& model,
                    const std::vector<LocatedExpr>& terms,
                    Diagnostics& diagnostics, const std::string& defaultFile) {
    return Checker(model, diagnostics).runTerms(terms, defaultFile);
}

} // namespace SOMTParser::Uir::Hir
