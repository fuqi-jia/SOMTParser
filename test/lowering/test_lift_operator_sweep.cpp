// One tiny SMT-LIB script per operator, round-tripped through the HIR.
//
// test_parser_to_hir.cpp establishes the property -- text -> Parser -> HIR ->
// Parser -> text, compared for equality -- on the constructs that had failed.
// This file applies it to the whole operator surface at once, because the
// defect this project keeps finding is not a broken operator but a TABLE
// NOBODY FINISHED, and a table is not something a hand-picked example set
// discovers. Three separate rounds of it:
//
//   * the regex cluster, the FP comparisons and `let` -- found by pointing the
//     frontend at test/instances/, which had been in the tree all along
//   * int2bv, fp.to_ubv, re.none, ubv_to_int -- found by reading the whole
//     NODE_KIND enum against the lift table, because no instance used them
//   * the Set SORT, to_fp, and every floating-point literal -- found by this
//     sweep, and none of them were reachable from either check above
//   * six standard operators the HIR did not have (rotate_left, rotate_right,
//     repeat, bvcomp, is_int, str.is_digit), and one -- `(_ divisible n)` --
//     the sweep could not even ask about until the ENGINE learned the standard
//     spelling, having had only a non-standard `is_divisible`
//
// The set gap is the one that argues for a sweep rather than another enum
// diff. All NINE set operators were correctly in the operator table and not
// one could ever run: a set term needs a set-sorted argument, `liftSort` had no
// line for `(Set T)`, and so every such script died at its DECLARATION. An enum
// diff over operators sees a full table. Only running one finds it.
//
// What each row asserts, via trips(): the script lifts, the lifted model
// type-checks, it lowers, and the text that comes back is EQUAL to what the
// engine prints for the input. Equal, not equivalent -- both sides go through
// the same printer, so any difference is a difference in the term.
//
// Rows are per operator rather than per family on purpose. `re.loop` was
// missing while the rest of the regex cluster was present, and a family-level
// row would have passed.

#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace H = SOMTParser::Uir::Hir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::string normalise(const std::string& src) {
    ParserPtr p = newParser();
    VERIFY(p->parseStr(src));
    return p->dumpSMT2();
}

/** text -> Parser -> HIR -> Parser -> text. */
std::string roundTrip(const std::string& src, bool& ok, std::string& why) {
    ParserPtr in = newParser();
    if (!in->parseStr(src)) { ok = false; why = "parse failed"; return ""; }

    Lower::ParserToHir up(in);
    H::ConstraintModel model;
    Diagnostics d;
    if (!up.lift(model, d)) {
        ok = false;
        why = d.all().empty() ? "lift failed" : d.all()[0].message;
        return "";
    }
    if (!typeCheck(model, d)) {
        ok = false;
        // The message matters here: a sort mistake in the lift prints fine,
        // because the printer does not type-check, so this is the only place
        // it can be caught.
        for (const Diagnostic& e : d.all()) {
            if (e.severity == Severity::ERROR) { why = e.message; }
        }
        if (why.empty()) { why = "lifted model does not type-check"; }
        return "";
    }
    ParserPtr out = newParser();
    Lower::HirToParser down(out);
    TranslationReport report;
    if (!down.lower(model, report, d)) {
        ok = false;
        why = "lowering the lifted model failed";
        return "";
    }
    ok = true;
    return out->dumpSMT2();
}

struct Case {
    const char* what;
    const char* decls;
    const char* body;
};

/** Declaration blocks, shared by the rows that need them. A row names only the
 *  sorts its own operator touches, so a sort the lift cannot read fails that
 *  row instead of the whole table -- which is how the missing `(Set T)` line
 *  originally hid, by failing every row at once with the same message. */
const char* kBool = "(declare-const p Bool)(declare-const q Bool)";
const char* kInt  = "(declare-const x Int)(declare-const y Int)";
const char* kReal = "(declare-const r Real)(declare-const s Real)";
const char* kBv   = "(declare-const b (_ BitVec 8))(declare-const c (_ BitVec 8))";
const char* kFp   = "(declare-const f (_ FloatingPoint 8 24))"
                    "(declare-const g (_ FloatingPoint 8 24))";
const char* kStr  = "(declare-const t String)(declare-const u String)";
const char* kArr  = "(declare-const a (Array Int Int))";
const char* kSet  = "(declare-const st (Set Int))";
/** A tuple is heterogeneous, so the prelude has to say so: a `(Tuple Int Int)`
 *  would let a row that confused field 0 with field 1 pass. */
const char* kTup  = "(declare-const tp (Tuple Int Bool))";
const char* kTup2 = "(declare-const tp (Tuple Int Bool))"
                    "(declare-const rp (Tuple Bool Int))";
const char* kUnitT = "(declare-const ut UnitTuple)";
const char* kFpBv = "(declare-const f (_ FloatingPoint 8 24))"
                    "(declare-const b (_ BitVec 8))";
/** The bit-pattern to_fp reinterprets rather than converts, so its argument
 *  is exactly the format's width -- 8 + 24 here, not the sweep's usual 8. */
const char* kFpBv32 = "(declare-const f (_ FloatingPoint 8 24))"
                      "(declare-const b32 (_ BitVec 32))";
const char* kFpR  = "(declare-const f (_ FloatingPoint 8 24))"
                    "(declare-const r Real)";
const char* kIntBv = "(declare-const x Int)(declare-const b (_ BitVec 8))";
const char* kStrInt = "(declare-const t String)(declare-const x Int)";
/** Three and four of a sort, for the chainable and right-associative rows. */
const char* kInt3 = "(declare-const x Int)(declare-const y Int)"
                    "(declare-const z Int)";
const char* kInt4 = "(declare-const x Int)(declare-const y Int)"
                    "(declare-const z Int)(declare-const w Int)";
const char* kBool3 = "(declare-const p Bool)(declare-const q Bool)"
                     "(declare-const s Bool)";
/** A recursive list, an enumeration, and a mutually recursive pair. */
const char* kLst = "(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))"
                   "(declare-const l Lst)";
const char* kEnum = "(declare-datatypes ((Color 0)) (((red) (green) (blue))))"
                    "(declare-const c Color)";
const char* kMutual =
    "(declare-datatypes ((T 0) (TL 0))"
    " (((node (kids TL)) (leaf (val Int))) ((tnil) (tcons (thd T) (ttl TL)))))"
    "(declare-const t T)";

std::size_t failures = 0;

void sweep(const std::vector<Case>& cases) {
    for (const Case& c : cases) {
        const std::string src = std::string("(set-logic ALL)\n") + c.decls
            + "\n(assert " + c.body + ")\n(check-sat)\n";
        bool ok = false;
        std::string why;
        const std::string back = roundTrip(src, ok, why);
        if (!ok) {
            std::cout << "  " << c.what << ": DOES NOT LIFT -- " << why << "\n";
            ++failures;
            continue;
        }
        const std::string want = normalise(src);
        if (back != want) {
            std::cout << "  " << c.what << ": ROUND TRIP DIFFERS\n"
                      << "--- expected ---\n" << want
                      << "--- got ---\n" << back;
            ++failures;
        }
    }
}

/** A construct with no HIR counterpart must be refused BY NAME -- never
 *  skipped, which would hand back a smaller model that type-checks and answers
 *  a different question with a success code. */
void refuses(const Case& c, const std::string& named) {
    const std::string src = std::string("(set-logic ALL)\n") + c.decls
        + "\n(assert " + c.body + ")\n(check-sat)\n";
    bool ok = false;
    std::string why;
    roundTrip(src, ok, why);
    if (ok) {
        std::cout << "  " << c.what << ": EXPECTED A REFUSAL\n";
        ++failures;
        return;
    }
    if (!has(why, named)) {
        std::cout << "  " << c.what << ": refusal did not name '" << named
                  << "': " << why << "\n";
        ++failures;
    }
}

} // namespace

int main() {
    std::cout << "======= lift: one row per operator =======\n";

    // ---- Core ---------------------------------------------------------------
    sweep({
        {"and", kBool, "(and p q)"},
        {"or", kBool, "(or p q)"},
        {"not", kBool, "(not p)"},
        {"xor", kBool, "(xor p q)"},
        {"=>", kBool, "(=> p q)"},
        {"=", kInt, "(= x y)"},
        {"distinct", kInt, "(distinct x y)"},
        {"ite", "(declare-const p Bool)(declare-const x Int)(declare-const y Int)",
         "(> (ite p x y) 0)"},
    });

    // ---- Arithmetic ---------------------------------------------------------
    //
    // `div` and `mod` lift to DIV_EUCLID and MOD_EUCLID, which is what SMT-LIB
    // means by them; the truncating and flooring members of the family have no
    // SMT-LIB spelling and so correctly have no row here.
    sweep({
        {"+", kInt, "(> (+ x y) 0)"},
        {"-", kInt, "(> (- x y) 0)"},
        {"*", kInt, "(> (* x y) 0)"},
        {"unary -", kInt, "(> (- x) 0)"},
        {"abs", kInt, "(> (abs x) 0)"},
        {"div", kInt, "(> (div x y) 0)"},
        {"mod", kInt, "(> (mod x y) 0)"},
        {"/", kReal, "(> (/ r s) 0.0)"},
        {"<=", kInt, "(<= x y)"},
        {"<", kInt, "(< x y)"},
        {">=", kInt, "(>= x y)"},
        {">", kInt, "(> x y)"},
        {"to_int", kReal, "(> (to_int r) 0)"},
        {"to_real", kInt, "(> (to_real x) 0.0)"},
        // A predicate, not a conversion: Real -> Bool.
        {"is_int", kReal, "(is_int r)"},
        // Indexed by the divisor. Both spellings the engine accepts build the
        // same node, so only one row is needed -- and the row after it checks
        // that they really do agree rather than assuming it.
        {"divisible", kInt, "((_ divisible 3) x)"},
        {"divisible, flat spelling", kInt, "(is_divisible x 3)"},
    });

    // ---- Arrays -------------------------------------------------------------
    sweep({
        {"select", kArr, "(> (select a 0) 0)"},
        {"store", kArr, "(= (store a 0 1) a)"},
        // `((as const (Array T U)) v)` is indexed by its RESULT SORT, like
        // int2bv: the value fixes U and says nothing about T. The two rows
        // below differ only in the index sort, which is what a lift that took
        // the sort from the value would collapse.
        {"constant array", kArr, "(= a ((as const (Array Int Int)) 0))"},
        {"constant array, other index sort",
         "(declare-const b (Array Bool Int))", "(= b ((as const (Array Bool Int)) 0))"},
    });

    // ---- Bit-vectors --------------------------------------------------------
    //
    // Every signed operator has an unsigned twin and vice versa, and they are
    // listed separately because the pair is exactly what a lift can silently
    // confuse: bvudiv and bvsdiv are the same bits read two ways.
    sweep({
        {"bvnot", kBv, "(= (bvnot b) c)"},
        {"bvneg", kBv, "(= (bvneg b) c)"},
        {"bvand", kBv, "(= (bvand b c) b)"},
        {"bvor", kBv, "(= (bvor b c) b)"},
        {"bvxor", kBv, "(= (bvxor b c) b)"},
        {"bvnand", kBv, "(= (bvnand b c) b)"},
        {"bvnor", kBv, "(= (bvnor b c) b)"},
        {"bvxnor", kBv, "(= (bvxnor b c) b)"},
        {"bvadd", kBv, "(= (bvadd b c) b)"},
        {"bvsub", kBv, "(= (bvsub b c) b)"},
        {"bvmul", kBv, "(= (bvmul b c) b)"},
        {"bvudiv", kBv, "(= (bvudiv b c) b)"},
        {"bvurem", kBv, "(= (bvurem b c) b)"},
        {"bvsdiv", kBv, "(= (bvsdiv b c) b)"},
        {"bvsrem", kBv, "(= (bvsrem b c) b)"},
        {"bvsmod", kBv, "(= (bvsmod b c) b)"},
        {"bvshl", kBv, "(= (bvshl b c) b)"},
        {"bvlshr", kBv, "(= (bvlshr b c) b)"},
        {"bvashr", kBv, "(= (bvashr b c) b)"},
        {"bvult", kBv, "(bvult b c)"},
        {"bvule", kBv, "(bvule b c)"},
        {"bvugt", kBv, "(bvugt b c)"},
        {"bvuge", kBv, "(bvuge b c)"},
        {"bvslt", kBv, "(bvslt b c)"},
        {"bvsle", kBv, "(bvsle b c)"},
        {"bvsgt", kBv, "(bvsgt b c)"},
        {"bvsge", kBv, "(bvsge b c)"},
        {"concat", kBv, "(= (concat b c) (concat c b))"},
        {"extract", kBv, "(= ((_ extract 3 0) b) #b0001)"},
        {"zero_extend", kBv, "(= ((_ zero_extend 4) b) ((_ zero_extend 4) c))"},
        {"sign_extend", kBv, "(= ((_ sign_extend 4) b) ((_ sign_extend 4) c))"},
        // Rotations are width-PRESERVING, unlike the two extensions they sit
        // beside in the indexed branch, and repeat multiplies. Three shapes
        // from one syntax, which is why the round trip is asserted for each
        // rather than for the branch.
        {"rotate_left", kBv, "(= ((_ rotate_left 2) b) c)"},
        {"rotate_right", kBv, "(= ((_ rotate_right 2) b) c)"},
        {"repeat", kBv, "(= ((_ repeat 2) b) ((_ repeat 2) c))"},
        // Result is a one-bit VECTOR, not a Bool -- so this row also checks
        // that the width did not come from the arguments.
        {"bvcomp", kBv, "(= (bvcomp b c) #b1)"},
        {"bv2nat", kBv, "(> (bv2nat b) 0)"},
        {"bv2int", kBv, "(> (bv2int b) 0)"},
        {"int2bv", kIntBv, "(= ((_ int2bv 8) x) b)"},
    });

    // ---- Floating point -----------------------------------------------------
    sweep({
        {"fp.add", kFp, "(= (fp.add RNE f g) f)"},
        {"fp.sub", kFp, "(= (fp.sub RNE f g) f)"},
        {"fp.mul", kFp, "(= (fp.mul RNE f g) f)"},
        {"fp.div", kFp, "(= (fp.div RNE f g) f)"},
        {"fp.fma", kFp, "(= (fp.fma RNE f g f) f)"},
        {"fp.sqrt", kFp, "(= (fp.sqrt RNE f) f)"},
        {"fp.roundToIntegral", kFp, "(= (fp.roundToIntegral RNE f) f)"},
        {"fp.abs", kFp, "(= (fp.abs f) f)"},
        {"fp.neg", kFp, "(= (fp.neg f) f)"},
        {"fp.rem", kFp, "(= (fp.rem f g) f)"},
        {"fp.min", kFp, "(= (fp.min f g) f)"},
        {"fp.max", kFp, "(= (fp.max f g) f)"},
        {"fp.leq", kFp, "(fp.leq f g)"},
        {"fp.lt", kFp, "(fp.lt f g)"},
        {"fp.geq", kFp, "(fp.geq f g)"},
        {"fp.gt", kFp, "(fp.gt f g)"},
        // IEEE equality, and NOT `=`. They are both Float x Float -> Bool and
        // they disagree on NaN and on signed zero -- the values floating-point
        // bugs live at -- so a lift that confused them would type-check.
        {"fp.eq", kFp, "(fp.eq f g)"},
        {"fp.isNormal", kFp, "(fp.isNormal f)"},
        {"fp.isSubnormal", kFp, "(fp.isSubnormal f)"},
        {"fp.isZero", kFp, "(fp.isZero f)"},
        {"fp.isInfinite", kFp, "(fp.isInfinite f)"},
        {"fp.isNaN", kFp, "(fp.isNaN f)"},
        {"fp.isNegative", kFp, "(fp.isNegative f)"},
        {"fp.isPositive", kFp, "(fp.isPositive f)"},
        {"fp.to_real", kFp, "(> (fp.to_real f) 0.0)"},
        {"fp.to_sbv", kFpBv, "(= ((_ fp.to_sbv 8) RTZ f) b)"},
        {"fp.to_ubv", kFpBv, "(= ((_ fp.to_ubv 8) RTZ f) b)"},
        {"to_fp from Real", kFpR, "(= ((_ to_fp 8 24) RNE r) f)"},
        {"to_fp from Float", kFp, "(= ((_ to_fp 8 24) RNE g) f)"},
        {"to_fp from BitVec", kFpBv, "(= ((_ to_fp 8 24) RNE b) f)"},
        {"to_fp_unsigned", kFpBv, "(= ((_ to_fp_unsigned 8 24) RNE b) f)"},
        // No rounding mode: REINTERPRETS the bits, the inverse of
        // fp.to_ieee_bv -- not the rounding form three characters away.
        {"to_fp bit reinterpretation", kFpBv32, "(= ((_ to_fp 8 24) b32) f)"},
    });

    // ---- Floating-point LITERALS --------------------------------------------
    //
    // Not one of these lifted, and the reason is worth keeping: the HIR's
    // LIT_FLOAT was required to be a DECIMAL numeral, which is the one spelling
    // an SMT-LIB script can never contain -- `1.5` is a Real. The two spellings
    // it can contain were both refused. NaN and infinity have no decimal form
    // at all; that is what they are for.
    sweep({
        {"fp bit triple", kFp,
         "(= f (fp #b0 #b10000000 #b00000000000000000000000))"},
        {"+oo", kFp, "(= f (_ +oo 8 24))"},
        {"-oo", kFp, "(= f (_ -oo 8 24))"},
        {"NaN", kFp, "(= f (_ NaN 8 24))"},
        {"+zero", kFp, "(= f (_ +zero 8 24))"},
        {"-zero", kFp, "(= f (_ -zero 8 24))"},
        // The engine folds this to a bit triple, so it is a literal by the time
        // the lift sees it rather than the conversion it looks like.
        {"to_fp of a constant", kFp, "(= f ((_ to_fp 8 24) RNE 1.5))"},
    });

    // ---- Strings ------------------------------------------------------------
    sweep({
        {"str.++", kStr, "(= (str.++ t u) t)"},
        {"str.len", kStr, "(> (str.len t) 0)"},
        {"str.at", kStr, "(= (str.at t 0) u)"},
        {"str.substr", kStr, "(= (str.substr t 0 1) u)"},
        {"str.indexof", kStr, "(> (str.indexof t u 0) 0)"},
        {"str.replace", kStr, "(= (str.replace t u t) t)"},
        {"str.replace_all", kStr, "(= (str.replace_all t u t) t)"},
        {"str.contains", kStr, "(str.contains t u)"},
        {"str.prefixof", kStr, "(str.prefixof t u)"},
        {"str.suffixof", kStr, "(str.suffixof t u)"},
        {"str.<", kStr, "(str.< t u)"},
        {"str.<=", kStr, "(str.<= t u)"},
        {"str.to_int", kStr, "(> (str.to_int t) 0)"},
        {"str.from_int", kStrInt, "(= (str.from_int x) t)"},
        {"str.to_code", kStr, "(> (str.to_code t) 0)"},
        {"str.from_code", kStrInt, "(= (str.from_code x) t)"},
        {"str.is_digit", kStr, "(str.is_digit t)"},
        // The three that take a REGULAR EXPRESSION where their plain
        // counterparts take a string. Separate operators, not overloads: the
        // second argument has a different sort, and confusing them looks for a
        // literal where the source asked for a language.
        {"str.indexof_re", kStr, R"((> (str.indexof_re t (str.to_re "a") 0) 0))"},
        {"str.replace_re", kStr, R"((= (str.replace_re t (str.to_re "a") u) t))"},
        {"str.replace_re_all", kStr,
         R"((= (str.replace_re_all t (str.to_re "a") u) t))"},
    });

    // ---- Regular expressions ------------------------------------------------
    //
    // The cluster that was missing wholesale, plus the three nullary ones that
    // are LITERALS rather than operators -- built as an ordinary constant
    // carrying a name, so only the SORT says what they are, and a check that
    // went by kind matched nothing.
    sweep({
        {"str.to_re / str.in_re", kStr, R"((str.in_re t (str.to_re "a")))"},
        {"re.++", kStr, R"((str.in_re t (re.++ (str.to_re "a") (str.to_re "b"))))"},
        {"re.union", kStr, R"((str.in_re t (re.union (str.to_re "a") (str.to_re "b"))))"},
        {"re.inter", kStr, R"((str.in_re t (re.inter (str.to_re "a") (str.to_re "b"))))"},
        {"re.diff", kStr, R"((str.in_re t (re.diff (str.to_re "a") (str.to_re "b"))))"},
        {"re.*", kStr, R"((str.in_re t (re.* (str.to_re "a"))))"},
        {"re.+", kStr, R"((str.in_re t (re.+ (str.to_re "a"))))"},
        {"re.opt", kStr, R"((str.in_re t (re.opt (str.to_re "a"))))"},
        {"re.comp", kStr, R"((str.in_re t (re.comp (str.to_re "a"))))"},
        {"re.range", kStr, R"((str.in_re t (re.range "a" "z")))"},
        {"re.loop", kStr, R"((str.in_re t ((_ re.loop 1 3) (str.to_re "a"))))"},
        {"re.none", kStr, "(str.in_re t re.none)"},
        {"re.all", kStr, "(str.in_re t re.all)"},
        {"re.allchar", kStr, "(str.in_re t re.allchar)"},
    });

    // ---- Finite sets --------------------------------------------------------
    //
    // Nine operators that were in the table and unreachable, because the SORT
    // they all take was not. See this file's header.
    sweep({
        {"set.singleton", kSet, "(= st (set.singleton 1))"},
        {"set.union", kSet, "(= (set.union st st) st)"},
        {"set.inter", kSet, "(= (set.inter st st) st)"},
        {"set.minus", kSet, "(= (set.minus st st) st)"},
        {"set.member", kSet, "(set.member 1 st)"},
        {"set.subset", kSet, "(set.subset st st)"},
        {"set.card", kSet, "(> (set.card st) 0)"},
        {"set.insert", kSet, "(= (set.insert 1 st) st)"},
        {"set.complement", kSet, "(= (set.complement st) st)"},
        {"set.empty", kSet, "(= st (as set.empty (Set Int)))"},
    });

    // ---- Tuples -------------------------------------------------------------
    //
    // The set gap again, one theory over: five NODE_KINDs, their builders and
    // their printer were in the engine, and `liftSort` had no line for
    // `(Tuple ...)`, so every one of them died at the declaration. See this
    // file's header -- an enum diff over OPERATORS cannot see this, because
    // the operators were not the thing that was missing.
    //
    // The prelude's fields are deliberately Int and Bool rather than two Ints:
    // `((_ tuple.select 0) tp)` and `((_ tuple.select 1) tp)` then have
    // different sorts, so a lift that dropped the index -- or kept it and read
    // the wrong field -- fails to type-check instead of round-tripping.
    sweep({
        {"tuple", kTup, "(= tp (tuple 1 true))"},
        {"tuple.unit", kUnitT, "(= ut tuple.unit)"},
        {"tuple.unit under distinct", kUnitT, "(distinct ut tuple.unit)"},
        {"tuple.select (Int field)", kTup, "(= ((_ tuple.select 0) tp) 1)"},
        {"tuple.select (Bool field)", kTup, "((_ tuple.select 1) tp)"},
        {"tuple.update", kTup, "(= ((_ tuple.update 0) tp 2) tp)"},
        {"tuple.project (reordering)", kTup2,
         "(= ((_ tuple.project 1 0) tp) rp)"},
        {"tuple.project (one field)",
         "(declare-const tp (Tuple Int Bool))(declare-const op (Tuple Int))",
         "(= ((_ tuple.project 0) tp) op)"},
    });

    // ---- Algebraic datatypes -------------------------------------------------
    //
    // The same shape as the set gap: SortKind::DATATYPE, DatatypeDecl and the
    // three expression kinds were all in the HIR, the lowering emitted them,
    // and the lift had NOTHING -- so a whole theory the IR carried could not be
    // read out of a script.
    //
    // Rows for the constructor, the selector and the tester separately, because
    // they are three expression kinds and not one: a tester is spelled `is-`
    // plus the constructor name in the engine and the bare name in the HIR, so
    // lifting the engine's spelling unchanged round-trips as `is-is-cons`.
    sweep({
        {"nullary constructor", kLst, "(= l nil)"},
        {"constructor with fields", kLst, "(= l (cons 2 nil))"},
        {"selector", kLst, "(= (hd l) 1)"},
        {"selector at the datatype sort", kLst, "(= (tl l) nil)"},
        {"tester", kLst, "((_ is cons) l)"},
        {"enumeration", kEnum, "(and (distinct c red) ((_ is green) c))"},
        // Mutual recursion: the declaration is one command and cannot be split,
        // which is a property of the DUMP rather than of the lift -- and the
        // round trip is what makes the two testable together.
        {"mutually recursive", kMutual, "(and ((_ is leaf) t) (= (val t) 3))"},
        {"nested constructors", kLst, "(= l (cons 1 (cons 2 nil)))"},
    });

    {
        // A datatype's members must not ALSO be uninterpreted functions.
        //
        // `(declare-datatypes ...)` registers a declare-fun for every
        // constructor, selector and tester, so getFunctions() returns `nil`,
        // `cons`, `hd`, `tl`, `is-nil` and `is-cons` beside the model's own
        // functions. Lifting those as FunDecls puts each symbol in the model
        // twice -- once in the DatatypeDecl and once beside it.
        //
        // The round trip cannot see this, which is why it is asserted here on
        // the MODEL: the engine's dumpSMT2 filters datatype members out of its
        // declare-fun emission, so the duplicate declarations vanish at print
        // time and the text comes back correct while the HIR is wrong. A
        // consumer that reads the model rather than the script -- which is
        // every pass in this project -- would see `hd` as a selector and as an
        // uninterpreted function at once.
        ParserPtr in = newParser();
        VERIFY(in->parseStr(
            "(set-logic ALL)\n"
            "(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n"
            "(declare-fun g (Int) Int)\n(declare-const l Lst)\n"
            "(assert (= (hd l) (g 1)))\n(check-sat)\n"));
        Lower::ParserToHir up(in);
        H::ConstraintModel model;
        Diagnostics d;
        VERIFY(up.lift(model, d));
        VERIFY(model.datatypes.size() == 1);
        // `g` and nothing else.
        if (model.funs.size() != 1 || model.funs[0].name != "g") {
            std::cout << "  datatype members leaked into model.funs:";
            for (const H::FunDecl& f : model.funs) { std::cout << " " << f.name; }
            std::cout << "\n";
            ++failures;
        }
    }

    // ---- SORTS, which the operator rows only reach incidentally --------------
    //
    // Every row above exercises the sorts its own operator needs, which is why
    // the missing `(Set T)` line showed up as ten failing set operators rather
    // than as one failing sort. These ask about the sort directly, so the next
    // omission names itself.
    sweep({
        {"uninterpreted sort", "(declare-sort U 0)(declare-const u U)", "(= u u)"},
        {"uninterpreted function over it",
         "(declare-sort U 0)(declare-fun f (U) U)(declare-const u U)", "(= (f u) u)"},
        // `(declare-sort S 1)` declares a CONSTRUCTOR, so these are three sorts
        // and not one. Flattening them to the constructor's name round-tripped
        // -- the script read back -- and merged them.
        {"applied sort constructor", "(declare-sort S 1)(declare-const x (S Bool))",
         "(= x x)"},
        {"a second instantiation",
         "(declare-sort S 1)(declare-const x (S Bool))(declare-const y (S Int))",
         "(and (= x x) (= y y))"},
        {"nested application",
         "(declare-sort S 1)(declare-const z (S (S Bool)))", "(= z z)"},
        {"arity 2", "(declare-sort Q 2)(declare-const q (Q Int Bool))", "(= q q)"},
        {"array of an applied sort",
         "(declare-sort S 1)(declare-const m (Array Int (S Bool)))"
         "(declare-const x (S Bool))",
         "(= (select m 0) x)"},
        {"nested arrays", "(declare-const a (Array Int (Array Int Int)))",
         "(= (select (select a 0) 0) 1)"},
        {"set of sets", "(declare-const s (Set (Set Int)))",
         "(set.member (set.singleton 1) s)"},
        {"tuple of tuples", "(declare-const n (Tuple (Tuple Int Bool) Int))",
         "(= ((_ tuple.select 1) n) 0)"},
        {"array of tuples",
         "(declare-const a (Array Int (Tuple Int Bool)))",
         "(= ((_ tuple.select 0) (select a 0)) 1)"},
        {"tuple holding a set and an array",
         "(declare-const v (Tuple (Set Int) (Array Int Int)))",
         "(set.member 1 ((_ tuple.select 0) v))"},
        {"array from bit-vector to float",
         "(declare-const a (Array (_ BitVec 8) (_ FloatingPoint 8 24)))",
         "(fp.isNaN (select a #x00))"},
        {"RoundingMode as a variable",
         "(declare-const rm RoundingMode)(declare-const f (_ FloatingPoint 8 24))",
         "(= (fp.add rm f f) f)"},
        {"RegLan as a variable",
         "(declare-const r RegLan)(declare-const t String)", "(str.in_re t r)"},
    });
    {
        // A `define-sort` alias is RESOLVED, so it is not in the sweep: the
        // round trip is exact and the text changes, like `let`. What must hold
        // is that both spellings arrive at one sort -- `b`, declared at the
        // alias, and `a`, declared at what it aliases.
        //
        // Compared against the lift's own output rather than the engine's,
        // because the engine's dump of this input emits a spurious
        // `(declare-sort SB 1)`: the alias is registered in the sort map and
        // the dump walks that map, so a define-sort comes back as a declared
        // sort of the aliased sort's arity, unused. The lift resolves the alias
        // and the extra declaration does not survive, which is the better
        // answer of the two.
        bool ok = false;
        std::string why;
        const std::string back = roundTrip(
            "(set-logic ALL)\n(declare-sort S 1)\n(define-sort SB () (S Bool))\n"
            "(declare-const a (S Bool))\n(declare-const b SB)\n"
            "(assert (= a b))\n(check-sat)\n", ok, why);
        if (!ok) {
            std::cout << "  define-sort alias does not lift: " << why << "\n";
            ++failures;
        } else {
            if (!has(back, "(declare-fun a () (S Bool))")
                || !has(back, "(declare-fun b () (S Bool))")) {
                std::cout << "  the alias did not resolve to (S Bool):\n" << back;
                ++failures;
            }
            if (has(back, "SB")) {
                std::cout << "  the alias survived into the output:\n" << back;
                ++failures;
            }
        }
    }
    {
        // Two instantiations of one constructor must not be interchangeable.
        // This is the property the whole sort dimension exists for, and it is
        // asserted at the ENGINE, because a script the engine rejects never
        // reaches the lift -- so a lift that merged them could not be caught by
        // a round trip alone.
        ParserPtr p = newParser();
        VERIFY(!p->parseStr("(set-logic ALL)\n(declare-sort S 1)\n"
                            "(declare-const x (S Bool))\n(declare-const y (S Int))\n"
                            "(assert (= x y))\n(check-sat)\n"));
    }

    // ---- SMT-LIB's argument-list attributes ---------------------------------
    //
    // `:chainable` and `:right-assoc` are what the standard says a three-or-more
    // argument list MEANS, not a leniency, so refusing one refuses a legal
    // script. The HIR's EQ, the orderings and IMPLIES are all binary, so the
    // lift expands -- and the expansion has to be the standard's: adjacent
    // pairs for a chain, RIGHT-nested for `=>`, because left-nesting `=>` is a
    // different truth table rather than a different spelling.
    //
    // These are round-trip rows like any other, so what they assert is that the
    // expansion is what the engine itself prints for the same input.
    sweep({
        {"<= with three arguments", kInt3, "(<= x y z)"},
        {"< with four arguments", kInt4, "(< x y z w)"},
        {">= with three arguments", kInt3, "(>= x y z)"},
    });
    {
        // `=` and `=>` are NOT in the sweep above, and the reason separates
        // them from the orderings beside them: the ENGINE expands a chained
        // ordering at parse time, so its own printed form already is the
        // conjunction and the round trip is textual. It keeps `(= x y z)` and
        // `(=> p q s)` as single n-ary nodes, so here the LIFT is what expands,
        // and the text changes -- exactly as `let` inlining changes it. The
        // expansion is what must be checked, not the equality.
        struct Chain { const char* what; const char* decls; const char* body;
                       const char* want; const char* absent; };
        const Chain chains[] = {
            // Adjacent pairs. `=` is transitive, so any spanning chain is
            // equivalent; adjacent is what the standard defines.
            {"= with three arguments", kInt3, "(= x y z)", "(= y z)", nullptr},
            // RIGHT-nested. `(=> (=> p q) s)` is a different truth table, not a
            // different spelling, so this row is the one that would catch a
            // fold written in the convenient direction.
            {"=> with three arguments", kBool3, "(=> p q s)",
             "(=> p (=> q s))", "(=> (=> p q) s)"},
        };
        for (const Chain& c : chains) {
            const std::string src = std::string("(set-logic ALL)\n") + c.decls
                + "\n(assert " + c.body + ")\n(check-sat)\n";
            bool ok = false;
            std::string why;
            const std::string back = roundTrip(src, ok, why);
            if (!ok) {
                std::cout << "  " << c.what << ": DOES NOT LIFT -- " << why << "\n";
                ++failures;
                continue;
            }
            if (!has(back, c.want)
                || (c.absent != nullptr && has(back, c.absent))) {
                std::cout << "  " << c.what << ": wrong expansion\n" << back;
                ++failures;
            }
            ParserPtr p = newParser();
            if (!p->parseStr(back)) {
                std::cout << "  " << c.what << ": expansion does not re-parse\n" << back;
                ++failures;
            }
        }
    }

    // ---- Binders ------------------------------------------------------------
    //
    // `let` is deliberately NOT in the sweep. It is the one construct that
    // round-trips without coming back as itself: SMT-LIB defines `let` by
    // substitution and the HIR has no binder for it, so the lift inlines. That
    // is exact and it costs size -- a value bound once and used twice is
    // written twice -- and it is pinned as its own property in
    // test/languages/test_smtlib2_instances.cpp. Equality of text is the wrong
    // question to ask of it; that it lifts at all is checked there.
    sweep({
        {"forall", "", "(forall ((z Int)) (> z 0))"},
        {"exists", "", "(exists ((z Int)) (> z 0))"},
    });

    // ---- The refusals, which must stay refusals and stay NAMED ---------------
    //
    // Each of these is a legal SMT-LIB term the engine reads and the HIR cannot
    // represent. What is asserted is not that they are unsupported -- that is a
    // known gap -- but that the gap surfaces as a message naming the construct,
    // rather than as a dropped constraint under a success code.
    // The engine permits a VARIABLE divisor as an extension; SMT-LIB's index is
    // a numeral. Lifting it as though the divisor were constant would fix it at
    // whatever value happened to be in the term.
    refuses({"divisible by a variable",
             "(declare-const x Int)(declare-const y Int)", "((_ divisible y) x)"},
            "non-constant divisor");

    if (failures != 0) {
        std::cout << failures << " operator(s) failed.\n";
        return 1;
    }
    std::cout << "All operator sweep tests passed." << std::endl;
    return 0;
}
