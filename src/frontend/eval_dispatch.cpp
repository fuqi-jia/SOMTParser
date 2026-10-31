/* -*- Source -*-
 *
 * OpDispatcher-based evaluation dispatch table.
 *
 * Author: Fuqi Jia <jiafq@ios.ac.cn>
 *
 * Copyright (C) 2025 Fuqi Jia
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#include "somtparser/frontend/eval_dispatch.h"
#include "somtparser/frontend/parser.h"

namespace SOMTParser {

// EvalAccess is friended by Parser, granting private evaluateXxx access.
struct EvalAccess {

#define H(NAME, METHOD) \
    static bool NAME(Node n, EvalContext& ctx) { \
        return ctx.parser->METHOD(n, ctx.model, *ctx.result); \
    }

    // Boolean
    H(h_and,       evaluateAnd)
    H(h_or,        evaluateOr)
    H(h_not,       evaluateNot)
    H(h_implies,   evaluateImpl)
    H(h_xor,       evaluateXor)
    H(h_eq,        evaluateEq)
    H(h_distinct,  evaluateDistinct)
    H(h_ite,       evaluateIte)

    // Arithmetic
    H(h_add,       evaluateAdd)
    H(h_neg,       evaluateNeg)
    H(h_sub,       evaluateSub)
    H(h_mul,       evaluateMul)
    H(h_div_int,   evaluateDivInt)
    H(h_div_real,  evaluateDivReal)
    H(h_mod,       evaluateMod)
    H(h_pow,       evaluatePow)
    H(h_pow2,      evaluatePow2)
    H(h_iand,      evaluateIand)
    H(h_abs,       evaluateAbs)
    H(h_sqrt,      evaluateSqrt)
    H(h_safesqrt,  evaluateSafeSqrt)
    H(h_ceil,      evaluateCeil)
    H(h_floor,     evaluateFloor)
    H(h_round,     evaluateRound)
    H(h_exp,       evaluateExp)
    H(h_ln,        evaluateLn)
    H(h_lg,        evaluateLg)
    H(h_log,       evaluateLog)
    H(h_lb,        evaluateLb)
    H(h_sin,       evaluateSin)
    H(h_cos,       evaluateCos)
    H(h_tan,       evaluateTan)
    H(h_cot,       evaluateCot)
    H(h_csc,       evaluateCsc)
    H(h_sec,       evaluateSec)
    H(h_asin,      evaluateAsin)
    H(h_acos,      evaluateAcos)
    H(h_atan,      evaluateAtan)
    H(h_acot,      evaluateAcot)
    H(h_asec,      evaluateAsec)
    H(h_acsc,      evaluateAcsc)
    H(h_atan2,     evaluateAtan2)
    H(h_sinh,      evaluateSinh)
    H(h_cosh,      evaluateCosh)
    H(h_tanh,      evaluateTanh)
    H(h_coth,      evaluateCoth)
    H(h_sech,      evaluateSech)
    H(h_csch,      evaluateCsch)
    H(h_asinh,     evaluateAsinh)
    H(h_acosh,     evaluateAcosh)
    H(h_atanh,     evaluateAtanh)
    H(h_asech,     evaluateAsech)
    H(h_acsch,     evaluateAcsch)
    H(h_acoth,     evaluateAcoth)
    H(h_le,        evaluateLe)
    H(h_lt,        evaluateLt)
    H(h_ge,        evaluateGe)
    H(h_gt,        evaluateGt)
    H(h_to_real,   evaluateToReal)
    H(h_to_int,    evaluateToInt)
    H(h_is_int,    evaluateIsInt)
    H(h_is_div,    evaluateIsDivisible)
    H(h_is_prime,  evaluateIsPrime)
    H(h_is_even,   evaluateIsEven)
    H(h_is_odd,    evaluateIsOdd)
    H(h_gcd,       evaluateGcd)
    H(h_lcm,       evaluateLcm)
    H(h_fact,      evaluateFact)
    H(h_max,       evaluateMax)
    H(h_min,       evaluateMin)

    // BitVector
    H(h_bv_not,    evaluateBvNot)
    H(h_bv_neg,    evaluateBvNeg)
    H(h_bv_and,    evaluateBvAnd)
    H(h_bv_or,     evaluateBvOr)
    H(h_bv_xor,    evaluateBvXor)
    H(h_bv_nand,   evaluateBvNand)
    H(h_bv_nor,    evaluateBvNor)
    H(h_bv_xnor,   evaluateBvXnor)
    H(h_bv_comp,   evaluateBvComp)
    H(h_bv_add,    evaluateBvAdd)
    H(h_bv_sub,    evaluateBvSub)
    H(h_bv_mul,    evaluateBvMul)
    H(h_bv_udiv,   evaluateBvUdiv)
    H(h_bv_urem,   evaluateBvUrem)
    H(h_bv_sdiv,   evaluateBvSdiv)
    H(h_bv_srem,   evaluateBvSrem)
    H(h_bv_smod,   evaluateBvSmod)
    H(h_bv_shl,    evaluateBvShl)
    H(h_bv_lshr,   evaluateBvLshr)
    H(h_bv_ashr,   evaluateBvAshr)
    H(h_bv_ult,    evaluateBvUlt)
    H(h_bv_ule,    evaluateBvUle)
    H(h_bv_ugt,    evaluateBvUgt)
    H(h_bv_uge,    evaluateBvUge)
    H(h_bv_slt,    evaluateBvSlt)
    H(h_bv_sle,    evaluateBvSle)
    H(h_bv_sgt,    evaluateBvSgt)
    H(h_bv_sge,    evaluateBvSge)
    H(h_bv_concat, evaluateBvConcat)
    H(h_bv_tonat,  evaluateBvToNat)
    H(h_nat_tobv,  evaluateBvNatToBv)
    H(h_int_tobv,  evaluateBvIntToBv)
    H(h_bv_toint,  evaluateBvToInt)
    H(h_bv_extract,   evaluateBvExtract)
    H(h_bv_repeat,    evaluateBvRepeat)
    H(h_bv_zero_ext,  evaluateBvZeroExt)
    H(h_bv_sign_ext,  evaluateBvSignExt)
    H(h_bv_rot_left,  evaluateBvRotLeft)
    H(h_bv_rot_right, evaluateBvRotRight)

    // Floating point
    H(h_fp_abs,       evaluateFpAbs)
    H(h_fp_neg,       evaluateFpNeg)
    H(h_fp_add,       evaluateFpAdd)
    H(h_fp_sub,       evaluateFpSub)
    H(h_fp_mul,       evaluateFpMul)
    H(h_fp_div,       evaluateFpDiv)
    H(h_fp_fma,       evaluateFpFma)
    H(h_fp_sqrt,      evaluateFpSqrt)
    H(h_fp_rem,       evaluateFpRem)
    H(h_fp_round,     evaluateFpRoundToIntegral)
    H(h_fp_min,       evaluateFpMin)
    H(h_fp_max,       evaluateFpMax)
    H(h_fp_le,        evaluateFpLe)
    H(h_fp_lt,        evaluateFpLt)
    H(h_fp_ge,        evaluateFpGe)
    H(h_fp_gt,        evaluateFpGt)
    H(h_fp_eq,        evaluateFpEq)
    H(h_fp_to_ubv,    evaluateFpToUbv)
    H(h_fp_to_sbv,    evaluateFpToSbv)
    H(h_fp_to_real,   evaluateFpToReal)
    H(h_to_fp,        evaluateToFp)
    H(h_to_fp_uns,    evaluateToFpUnsigned)
    H(h_fp_is_norm,   evaluateFpIsNormal)
    H(h_fp_is_sub,    evaluateFpIsSubnormal)
    H(h_fp_is_zero,   evaluateFpIsZero)
    H(h_fp_is_inf,    evaluateFpIsInf)
    H(h_fp_is_nan,    evaluateFpIsNaN)
    H(h_fp_is_neg,    evaluateFpIsNeg)
    H(h_fp_is_pos,    evaluateFpIsPos)

    // Array
    H(h_select,       evaluateSelect)
    H(h_store,        evaluateStore)
    H(h_const_array,  evaluateConstArray)

    // String
    H(h_str_len,      evaluateStrLen)
    H(h_str_concat,   evaluateStrConcat)
    H(h_str_substr,   evaluateStrSubstr)
    H(h_str_prefix,   evaluateStrPrefixof)
    H(h_str_suffix,   evaluateStrSuffixof)
    H(h_str_indexof,  evaluateStrIndexof)
    H(h_str_charat,   evaluateStrCharat)
    H(h_str_update,   evaluateStrUpdate)
    H(h_str_replace,  evaluateStrReplace)
    H(h_str_repl_all, evaluateStrReplaceAll)
    H(h_str_tolower,  evaluateStrToLower)
    H(h_str_toupper,  evaluateStrToUpper)
    H(h_str_rev,      evaluateStrRev)
    H(h_str_split,    evaluateStrSplit)
    // evaluateStrSplitAt not implemented; route through evaluateSimpleOp
    H(h_str_split_rest, evaluateStrSplitRest)
    // evaluateStrNumSplits not implemented; route through evaluateSimpleOp
    H(h_str_split_re, evaluateStrSplitAtRe)
    H(h_str_split_rest_re, evaluateStrSplitRestRe)
    H(h_str_num_splits_re, evaluateStrNumSplitsRe)
    H(h_str_lt,       evaluateStrLt)
    H(h_str_le,       evaluateStrLe)
    H(h_str_gt,       evaluateStrGt)
    H(h_str_ge,       evaluateStrGe)
    H(h_str_in_reg,   evaluateStrInReg)
    H(h_str_contains, evaluateStrContains)
    H(h_str_isdigit,  evaluateStrIsDigit)
    H(h_str_fromint,  evaluateStrFromInt)
    H(h_str_toint,    evaluateStrToInt)
    H(h_str_toreg,    evaluateStrToReg)
    H(h_str_tocode,   evaluateStrToCode)
    H(h_str_fromcode, evaluateStrFromCode)

    // Regex
    H(h_reg_concat,   evaluateRegConcat)
    H(h_reg_union,    evaluateRegUnion)
    H(h_reg_inter,    evaluateRegInter)
    H(h_reg_diff,     evaluateRegDiff)
    H(h_reg_star,     evaluateRegStar)
    H(h_reg_plus,     evaluateRegPlus)
    H(h_reg_opt,      evaluateRegOpt)
    H(h_reg_range,    evaluateRegRange)
    H(h_reg_repeat,   evaluateRegRepeat)
    H(h_reg_complement, evaluateRegComplement)

#undef H

    // Manual handlers that call evaluateSimpleOp
    static bool h_reg_loop(Node n, EvalContext& ctx) {
        return ctx.parser->evaluateSimpleOp(n, ctx.model, *ctx.result, NODE_KIND::NT_REG_LOOP);
    }
    static bool h_str_replace_reg(Node n, EvalContext& ctx) {
        return ctx.parser->evaluateSimpleOp(n, ctx.model, *ctx.result, NODE_KIND::NT_STR_REPLACE_REG);
    }
    static bool h_str_replace_reg_all(Node n, EvalContext& ctx) {
        return ctx.parser->evaluateSimpleOp(n, ctx.model, *ctx.result, NODE_KIND::NT_STR_REPLACE_REG_ALL);
    }
    static bool h_str_indexof_reg(Node n, EvalContext& ctx) {
        return ctx.parser->evaluateSimpleOp(n, ctx.model, *ctx.result, NODE_KIND::NT_STR_INDEXOF_REG);
    }
    static bool h_str_split_at(Node n, EvalContext& ctx) {
        return ctx.parser->evaluateSimpleOp(n, ctx.model, *ctx.result, NODE_KIND::NT_STR_SPLIT_AT);
    }
    static bool h_str_num_splits(Node n, EvalContext& ctx) {
        return ctx.parser->evaluateSimpleOp(n, ctx.model, *ctx.result, NODE_KIND::NT_STR_NUM_SPLITS);
    }

    // Datatype
    static bool h_dt_ctor(Node n, EvalContext& ctx) { return ctx.parser->evaluateDtConstructor(n, ctx.model, *ctx.result); }
    static bool h_dt_sel(Node n, EvalContext& ctx) { return ctx.parser->evaluateDtSelector(n, ctx.model, *ctx.result); }
    static bool h_dt_tester(Node n, EvalContext& ctx) { return ctx.parser->evaluateDtTester(n, ctx.model, *ctx.result); }
    static bool h_dt_match(Node n, EvalContext& ctx) { return ctx.parser->evaluateMatch(n, ctx.model, *ctx.result); }

    // UF / Function application
    static bool h_uf_apply(Node n, EvalContext& ctx) { return ctx.parser->evaluateUFApply(n, ctx.model, *ctx.result); }
    static bool h_func_apply(Node n, EvalContext& ctx) { return ctx.parser->evaluateApplyFun(n, ctx.model, *ctx.result); }

    // Let
    static bool h_let(Node n, EvalContext& ctx) { return ctx.parser->evaluateLet(n, ctx.model, *ctx.result); }
};

// ─── Build dispatch table (called once) ──────────────────────────────────

using A = EvalAccess;

static OpDispatcher<bool, EvalContext> buildEvalDispatcher() {
    OpDispatcher<bool, EvalContext> d;

    // Boolean
    d.onAND(A::h_and).onOR(A::h_or).onNOT(A::h_not).onIMPLIES(A::h_implies).onXOR(A::h_xor);
    d.onEQ(A::h_eq).onDISTINCT(A::h_distinct).onITE(A::h_ite);
    // The IR also carries typed equality/distinct kinds. They have the same
    // semantics and operand traversal as the generic spelling; falling back
    // here silently returns a symbolic term even under a complete model.
    d.on(NODE_KIND::NT_EQ_BOOL, A::h_eq).on(NODE_KIND::NT_EQ_OTHER, A::h_eq);
    d.on(NODE_KIND::NT_DISTINCT_BOOL, A::h_distinct).on(NODE_KIND::NT_DISTINCT_OTHER, A::h_distinct);

    // Arithmetic
    d.onADD(A::h_add).on(NODE_KIND::NT_NEG, A::h_neg).onSUB(A::h_sub).onMUL(A::h_mul);
    d.onDIV_INT(A::h_div_int).onDIV_REAL(A::h_div_real).onMOD(A::h_mod);
    d.onPOW(A::h_pow).onPOW2(A::h_pow2).onIAND(A::h_iand);
    d.onABS(A::h_abs).onSQRT(A::h_sqrt).onSAFESQRT(A::h_safesqrt);
    d.onCEIL(A::h_ceil).onFLOOR(A::h_floor).onROUND(A::h_round);
    d.onEXP(A::h_exp).onLN(A::h_ln).onLG(A::h_lg).onLOG(A::h_log).onLB(A::h_lb);
    d.onSIN(A::h_sin).onCOS(A::h_cos).onTAN(A::h_tan);
    d.onCOT(A::h_cot).onCSC(A::h_csc).onSEC(A::h_sec);
    d.onASIN(A::h_asin).onACOS(A::h_acos).onATAN(A::h_atan);
    d.onACOT(A::h_acot).onASEC(A::h_asec).onACSC(A::h_acsc);
    d.onATAN2(A::h_atan2);
    d.onSINH(A::h_sinh).onCOSH(A::h_cosh).onTANH(A::h_tanh);
    d.onCOTH(A::h_coth).onSECH(A::h_sech).onCSCH(A::h_csch);
    d.onASINH(A::h_asinh).onACOSH(A::h_acosh).onATANH(A::h_atanh);
    d.onASECH(A::h_asech).onACSCH(A::h_acsch).onACOTH(A::h_acoth);
    d.onLE(A::h_le).onLT(A::h_lt).onGE(A::h_ge).onGT(A::h_gt);
    d.onTO_REAL(A::h_to_real).onTO_INT(A::h_to_int);
    d.onIS_INT(A::h_is_int).onIS_DIVISIBLE(A::h_is_div);
    d.onIS_PRIME(A::h_is_prime).onIS_EVEN(A::h_is_even).onIS_ODD(A::h_is_odd);
    d.onGCD(A::h_gcd).onLCM(A::h_lcm).onFACT(A::h_fact);
    d.on(NODE_KIND::NT_MAX, A::h_max).on(NODE_KIND::NT_MIN, A::h_min);

    // BitVector
    d.onBV_NOT(A::h_bv_not).onBV_NEG(A::h_bv_neg);
    d.onBV_AND(A::h_bv_and).onBV_OR(A::h_bv_or).onBV_XOR(A::h_bv_xor);
    d.onBV_NAND(A::h_bv_nand).onBV_NOR(A::h_bv_nor).onBV_XNOR(A::h_bv_xnor).onBV_COMP(A::h_bv_comp);
    d.onBV_ADD(A::h_bv_add).onBV_SUB(A::h_bv_sub).onBV_MUL(A::h_bv_mul);
    d.onBV_UDIV(A::h_bv_udiv).onBV_UREM(A::h_bv_urem);
    d.onBV_SDIV(A::h_bv_sdiv).onBV_SREM(A::h_bv_srem).onBV_SMOD(A::h_bv_smod);
    d.onBV_SHL(A::h_bv_shl).onBV_LSHR(A::h_bv_lshr).onBV_ASHR(A::h_bv_ashr);
    d.onBV_ULT(A::h_bv_ult).onBV_ULE(A::h_bv_ule).onBV_UGT(A::h_bv_ugt).onBV_UGE(A::h_bv_uge);
    d.onBV_SLT(A::h_bv_slt).onBV_SLE(A::h_bv_sle).onBV_SGT(A::h_bv_sgt).onBV_SGE(A::h_bv_sge);
    d.onBV_CONCAT(A::h_bv_concat);
    d.onBV_TO_NAT(A::h_bv_tonat).onNAT_TO_BV(A::h_nat_tobv).onINT_TO_BV(A::h_int_tobv).onBV_TO_INT(A::h_bv_toint);
    d.onBV_EXTRACT(A::h_bv_extract).onBV_REPEAT(A::h_bv_repeat);
    d.onBV_ZERO_EXT(A::h_bv_zero_ext).onBV_SIGN_EXT(A::h_bv_sign_ext);
    d.onBV_ROTATE_LEFT(A::h_bv_rot_left).onBV_ROTATE_RIGHT(A::h_bv_rot_right);

    // Floating point
    d.onFP_ABS(A::h_fp_abs).onFP_NEG(A::h_fp_neg);
    d.onFP_ADD(A::h_fp_add).onFP_SUB(A::h_fp_sub).onFP_MUL(A::h_fp_mul).onFP_DIV(A::h_fp_div);
    d.onFP_FMA(A::h_fp_fma).onFP_SQRT(A::h_fp_sqrt).onFP_REM(A::h_fp_rem);
    d.onFP_ROUND_TO_INTEGRAL(A::h_fp_round).onFP_MIN(A::h_fp_min).onFP_MAX(A::h_fp_max);
    d.onFP_LE(A::h_fp_le).onFP_LT(A::h_fp_lt).onFP_GE(A::h_fp_ge).onFP_GT(A::h_fp_gt).onFP_EQ(A::h_fp_eq);
    d.onFP_TO_UBV(A::h_fp_to_ubv).onFP_TO_SBV(A::h_fp_to_sbv).onFP_TO_REAL(A::h_fp_to_real);
    d.onFP_TO_FP(A::h_to_fp).onFP_TO_FP_UNSIGNED(A::h_to_fp_uns);
    d.onFP_IS_NORMAL(A::h_fp_is_norm).onFP_IS_SUBNORMAL(A::h_fp_is_sub);
    d.onFP_IS_ZERO(A::h_fp_is_zero).onFP_IS_INF(A::h_fp_is_inf).onFP_IS_NAN(A::h_fp_is_nan);
    d.onFP_IS_NEG(A::h_fp_is_neg).onFP_IS_POS(A::h_fp_is_pos);

    // Array
    d.onSELECT(A::h_select).onSTORE(A::h_store);
    d.on(NODE_KIND::NT_CONST_ARRAY, A::h_const_array);

    // String
    d.onSTR_LEN(A::h_str_len).onSTR_CONCAT(A::h_str_concat).onSTR_SUBSTR(A::h_str_substr);
    d.onSTR_PREFIXOF(A::h_str_prefix).onSTR_SUFFIXOF(A::h_str_suffix);
    d.onSTR_INDEXOF(A::h_str_indexof).onSTR_CHARAT(A::h_str_charat).onSTR_UPDATE(A::h_str_update);
    d.onSTR_REPLACE(A::h_str_replace).onSTR_REPLACE_ALL(A::h_str_repl_all);
    d.onSTR_REPLACE_REG(A::h_str_replace_reg).onSTR_REPLACE_REG_ALL(A::h_str_replace_reg_all);
    d.onSTR_INDEXOF_REG(A::h_str_indexof_reg);
    d.onSTR_TO_LOWER(A::h_str_tolower).onSTR_TO_UPPER(A::h_str_toupper).onSTR_REV(A::h_str_rev);
    d.onSTR_SPLIT(A::h_str_split).onSTR_SPLIT_AT(A::h_str_split_at);
    d.onSTR_SPLIT_REST(A::h_str_split_rest).onSTR_NUM_SPLITS(A::h_str_num_splits);
    d.onSTR_SPLIT_AT_RE(A::h_str_split_re).onSTR_SPLIT_REST_RE(A::h_str_split_rest_re).onSTR_NUM_SPLITS_RE(A::h_str_num_splits_re);
    d.onSTR_LT(A::h_str_lt).onSTR_LE(A::h_str_le).onSTR_GT(A::h_str_gt).onSTR_GE(A::h_str_ge);
    d.onSTR_IN_REG(A::h_str_in_reg).onSTR_CONTAINS(A::h_str_contains).onSTR_IS_DIGIT(A::h_str_isdigit);
    d.onSTR_FROM_INT(A::h_str_fromint).onSTR_TO_INT(A::h_str_toint);
    d.onSTR_TO_REG(A::h_str_toreg).onSTR_TO_CODE(A::h_str_tocode).onSTR_FROM_CODE(A::h_str_fromcode);

    // Regex
    d.onREG_CONCAT(A::h_reg_concat).onREG_UNION(A::h_reg_union).onREG_INTER(A::h_reg_inter).onREG_DIFF(A::h_reg_diff);
    d.onREG_STAR(A::h_reg_star).onREG_PLUS(A::h_reg_plus).onREG_OPT(A::h_reg_opt);
    d.onREG_RANGE(A::h_reg_range).onREG_REPEAT(A::h_reg_repeat).onREG_LOOP(A::h_reg_loop);
    d.onREG_COMPLEMENT(A::h_reg_complement);

    // Datatype
    d.on(NODE_KIND::NT_DT_CONSTRUCTOR, A::h_dt_ctor);
    d.on(NODE_KIND::NT_DT_SELECTOR, A::h_dt_sel);
    d.on(NODE_KIND::NT_DT_TESTER, A::h_dt_tester);
    d.on(NODE_KIND::NT_DT_MATCH, A::h_dt_match);

    // UF / Functions
    d.on(NODE_KIND::NT_UF_APPLY, A::h_uf_apply);
    d.on(NODE_KIND::NT_FUNC_APPLY, A::h_func_apply);

    // Let
    d.on(NODE_KIND::NT_LET, A::h_let);
    d.on(NODE_KIND::NT_LET_CHAIN, A::h_let);

    // Fallback: return expression unchanged
    d.otherwise([](Node n, EvalContext& ctx) -> bool {
        *ctx.result = n;
        return false;
    });

    return d;
}

const OpDispatcher<bool, EvalContext>& getEvalDispatcher() {
    static const OpDispatcher<bool, EvalContext> instance = buildEvalDispatcher();
    return instance;
}

} // namespace SOMTParser
