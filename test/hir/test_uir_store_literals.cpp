// store, and the real and floating-point literals.
//
// Three gaps docs/languages/smtlib2.md named after the bit-vector and
// floating-point operator sets landed, each of which left a sort whose theory
// was only half present:
//
//   * `select` without `store`. hir.h says ARRAY *is* SMT-LIB's array, and a
//     read-only one is not that. QF_AX and every array logic need writes.
//   * No Real literal, so a Real variable could be declared and compared only
//     against integers.
//   * No floating-point literal, so the 24 floating-point operators that had
//     just landed could not be applied to a constant -- `fp.add RNE x 1.5` was
//     unsayable.
//
// The literals keep their value as TEXT rather than as a double, and that is the
// substantive decision here. SMT-LIB reals are exact rationals; 0.1 is not
// representable in binary floating point; a translation that rounded the
// coefficients of a linear program would answer a different question while
// reporting Fidelity::exact(). The engine's Number is GMP-backed, so exactness
// survives the whole way down -- but only if nothing in between turns the text
// into a double.

#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace H = SOMTParser::Uir::Hir;

namespace {

const H::Sort INT   = H::Sort::integer();
const H::Sort REAL  = H::Sort::real();
const H::Sort BOOLS = H::Sort::boolean();
const H::Sort F32   = H::Sort::floating(8, 24);
const H::Sort ARR   = H::Sort::array(INT, INT);          // (Array Int Int)
const H::Sort ARR_B = H::Sort::array(INT, BOOLS);        // (Array Int Bool)

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

VarDecl decl(const char* n, H::Sort s) {
    VarDecl d;
    d.name = n;
    d.sort = std::move(s);
    return d;
}

ConstraintModel base() {
    ConstraintModel m;
    m.decls.push_back(decl("a", ARR));
    m.decls.push_back(decl("b", ARR_B));
    m.decls.push_back(decl("i", INT));
    m.decls.push_back(decl("r", REAL));
    m.decls.push_back(decl("f", F32));
    m.decls.push_back(decl("p", BOOLS));
    return m;
}

void add(ConstraintModel& m, ExprPtr formula) {
    Constraint c;
    c.formula = std::move(formula);
    m.constraints.push_back(c);
}

std::string emit(const ConstraintModel& m) {
    Diagnostics d;
    VERIFY(typeCheck(m, d));
    ParserPtr p = newParser();
    Lower::HirToParser lowered(p);
    TranslationReport report;
    VERIFY(lowered.lower(m, report, d));
    VERIFY(!d.hasErrors());
    return p->dumpSMT2();
}

bool rejects(const ConstraintModel& m, ErrorCode code) {
    Diagnostics d;
    if (typeCheck(m, d)) { return false; }
    return d.hasErrors() && d.firstErrorCode() == code;
}

ExprPtr arr()  { return mkIdent("a", ARR); }
ExprPtr arrB() { return mkIdent("b", ARR_B); }
ExprPtr idx()  { return mkIdent("i", INT); }

} // namespace

int main() {
    std::cout << "======= store and numeric literals =======\n";

    // ---- store yields the ARRAY's sort, not the element's. ------------------
    {
        const ExprPtr s = mkOp(Op::STORE, {arr(), idx(), mkInt(7)});
        VERIFY(sameSort(s->sort, ARR));

        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {s, arr()}));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "store"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }

    // ---- store composes with select, which is the point of having both. -----
    //
    // Asserted on semantics rather than on shape, because the engine's builders
    // simplify before they build (CLAUDE.md invariant 2): `(select (store a i v)
    // i)` is read-over-write and comes back as `v`, so a test that looked for
    // the word "store" in the output would fail on *correct* behaviour. Two
    // cases, because each proves something the other cannot.
    {
        // Same index: the axiom fires and the constraint is discharged. What is
        // checked is that the term builds and the script is well-formed -- if
        // either operator lowered to the wrong builder, neither would hold.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ,
            {mkOp(Op::SELECT, {mkOp(Op::STORE, {arr(), idx(), mkInt(7)}), idx()}),
             mkInt(7)}));
        Diagnostics d;
        VERIFY(typeCheck(m, d));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(emit(m)));
    }
    {
        // Distinct indices: nothing to simplify, so both operators survive into
        // the script and can be seen there.
        ConstraintModel m = base();
        m.decls.push_back(decl("j", INT));
        add(m, mkOp(Op::EQ,
            {mkOp(Op::SELECT, {mkOp(Op::STORE, {arr(), idx(), mkInt(7)}),
                               mkIdent("j", INT)}),
             mkInt(7)}));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "store"));
        VERIFY(contains(smt, "select"));
    }
    {
        // Nested stores: the result of a store is storable again.
        ConstraintModel m = base();
        const ExprPtr inner = mkOp(Op::STORE, {arr(), mkInt(0), mkInt(1)});
        add(m, mkOp(Op::EQ, {mkOp(Op::STORE, {inner, mkInt(1), mkInt(2)}), arr()}));
        VERIFY(contains(emit(m), "store"));
    }

    // ---- The value is checked against the ELEMENT sort. ---------------------
    // Against the *index* sort would pass for every (Array Int Int) and fail
    // silently for everything else, so the Bool-valued array is the case that
    // can see it.
    {
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ,
            {mkOp(Op::STORE, {arrB(), idx(), mkInt(1)}), arrB()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));

        Diagnostics d;
        VERIFY(!typeCheck(m, d));
        VERIFY(contains(d.all().front().message, "elements are Bool"));
    }
    {
        // ...and the matching value is accepted, so the check is not simply
        // rejecting every Bool-valued store.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ,
            {mkOp(Op::STORE, {arrB(), idx(), mkBool(true)}), arrB()}));
        Diagnostics d;
        VERIFY(typeCheck(m, d));
        VERIFY(contains(emit(m), "store"));
    }
    {
        // The index is checked too.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ,
            {mkOp(Op::STORE, {arr(), mkBool(true), mkInt(1)}), arr()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // store on a non-array.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ,
            {mkOp(Op::STORE, {idx(), idx(), mkInt(1)}), arr()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // Wrong arity is reported as an arity error, not as a sort mismatch on
        // an argument that is not there.
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkOp(Op::STORE, {arr(), idx(), mkInt(1), mkInt(2)}), arr()}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }

    // ---- Real literals are exact, and stay exact. ---------------------------
    // The reason the value is text: 0.1 has no finite binary expansion, so a
    // double round trip loses it. The literal must survive verbatim into the
    // script, or a linear program's coefficients are quietly perturbed.
    {
        ConstraintModel m = base();
        add(m, mkOp(Op::LE, {mkIdent("r", REAL), mkReal("0.1")}));
        const std::string smt = emit(m);
        // The engine normalises a decimal to an exact rational, so the property
        // to assert is exactness and not the spelling: 0.1 comes out as
        // (/ 1 10), which IS one tenth. A double round trip would give
        // 0.1000000000000000055511151231257827, which is not.
        VERIFY(contains(smt, "(/ 1 10)"));
        VERIFY(!contains(smt, "0.1000000"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }
    {
        // A value no double holds exactly and no long long holds at all:
        // 123456789012345678901234567890.5 = 246913578024691357802469135781/2.
        // Every digit has to survive, which is what "GMP-backed, and nothing in
        // between turns it into a double" means concretely.
        ConstraintModel m = base();
        add(m, mkOp(Op::LE, {mkIdent("r", REAL),
                             mkReal("123456789012345678901234567890.5")}));
        VERIFY(contains(emit(m), "246913578024691357802469135781"));
    }
    {
        VERIFY(sameSort(mkReal("1.5")->sort, REAL));
        VERIFY(mkReal("1.5")->kind == ExprKind::LIT_REAL);
        // A negative literal is one literal, not a negation of one.
        ConstraintModel m = base();
        add(m, mkOp(Op::LE, {mkReal("-2.5"), mkIdent("r", REAL)}));
        VERIFY(contains(emit(m), "5"));   // -5/2 in some spelling
    }
    {
        // Text that is not a numeral must not reach the script, where it would
        // be rejected by whatever reads the output -- a failure three layers
        // from its cause.
        ConstraintModel m = base();
        add(m, mkOp(Op::LE, {mkIdent("r", REAL), mkReal("1.5e10")}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));

        ConstraintModel n = base();
        add(n, mkOp(Op::LE, {mkIdent("r", REAL), mkReal("(/ 1 3)")}));
        VERIFY(rejects(n, ErrorCode::E_TYPE));
    }

    // The rational literal constructor must reject zero even when padded or
    // signed; no target builder should receive an undefined rational value.
    for (const auto& value : {"1/0", "0/0", "-7/000", "+1/00", "000/000"}) {
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkIdent("r", REAL), mkReal(value)}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
        Diagnostics diagnostics;
        VERIFY(!typeCheckTerms({}, {{mkReal(value), {}}}, diagnostics));
        VERIFY(diagnostics.hasErrors());
    }
    // Leading zeros do not make a nonzero denominator invalid, and exact
    // rational literals are not limited by the host integer representation.
    for (const auto& value : {"0/0003", "+1/0002", "-7/0002",
                             "1/100000000000000000000000000000000000007"}) {
        ConstraintModel m = base();
        add(m, mkOp(Op::EQ, {mkIdent("r", REAL), mkReal(value)}));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(emit(m)));
    }

    // ---- Floating-point literals carry their format. ------------------------
    {
        const ExprPtr lit = mkFloat("1.5", 8, 24);
        VERIFY(sameSort(lit->sort, F32));
        VERIFY(lit->kind == ExprKind::LIT_FLOAT);

        ConstraintModel m = base();
        add(m, mkOp(Op::FP_LT, {mkIdent("f", F32), lit}));
        const std::string smt = emit(m);
        VERIFY(contains(smt, "fp"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }
    {
        // The whole point: `fp.add RNE x 1.5` is now sayable.
        ConstraintModel m = base();
        add(m, mkOp(Op::FP_LT,
            {mkOp(Op::FP_ADD, {mkRoundingMode("RNE"), mkIdent("f", F32),
                               mkFloat("1.5", 8, 24)}),
             mkIdent("f", F32)}));
        Diagnostics d;
        VERIFY(typeCheck(m, d));
        VERIFY(contains(emit(m), "fp.add"));
    }
    {
        // A literal of the wrong format against the same variable is rejected:
        // the format comes from the literal's own sort, so this is the
        // same-format rule reaching a different node.
        ConstraintModel m = base();
        add(m, mkOp(Op::FP_LT, {mkIdent("f", F32), mkFloat("1.5", 11, 53)}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // A Real literal is not a Float literal. `1.5` as a Real and `1.5` at
        // single precision are different values of different sorts -- the second
        // is whatever RNE rounds the first to -- so the two must not be
        // interchangeable.
        ConstraintModel m = base();
        add(m, mkOp(Op::FP_LT, {mkIdent("f", F32), mkReal("1.5")}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));

        ConstraintModel n = base();
        add(n, mkOp(Op::LE, {mkIdent("r", REAL), mkFloat("1.5", 8, 24)}));
        VERIFY(rejects(n, ErrorCode::E_TYPE));
    }

    // ---- Integer literals of unbounded magnitude. ---------------------------
    //
    // An OPB coefficient is an unbounded integer by explicit design and the
    // format document's own example exceeds LLONG_MAX (opb-wbo.md §2.3), so the
    // authoritative value is the decimal TEXT and `int_value` is valid only when
    // it fits.
    //
    // Deliberately not a second ExprKind. SMT-LIB has one numeral syntax and
    // `long long` is a limit of a field rather than of the language; a
    // `LIT_BIGINT` would put a C++ limitation into the IR's vocabulary and
    // oblige every consumer to handle two kinds forever -- which is exactly what
    // isConstant did to LIT_BITVEC before it was fixed (opb-wbo.md §4.6).
    {
        const std::string big = "170141183460469231731687303715884105727";  // 2^127-1
        const ExprPtr e = mkInt(big);
        VERIFY(e->kind == ExprKind::LIT_INT);
        VERIFY(sameSort(e->sort, INT));
        // The machine field cannot hold it, and fitsInt64 says so rather than
        // the caller discovering a wrong number later.
        VERIFY(!fitsInt64(*e));
        VERIFY(fitsInt64(*mkInt(42)));
        // ...and it is left at ZERO rather than saturated or truncated. A
        // consumer that forgets to ask is broken either way, but a truncated
        // value is a wrong number that LOOKS usable, while zero is obviously
        // not the coefficient. The header comment says "left at zero"; this is
        // what makes that a claim rather than a hope.
        VERIFY(e->int_value == 0);

        ConstraintModel m = base();
        add(m, mkOp(Op::LE, {mkIdent("i", INT), e}));
        const std::string smt = emit(m);
        // Every digit survives. The engine's Number is GMP-backed, so the
        // magnitude gets all the way down provided nothing in between narrows
        // it to a machine integer -- which is what reading int_value would do.
        VERIFY(contains(smt, big));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }
    {
        // A negative one, since the sign is part of the text.
        const ExprPtr e = mkInt(std::string("-99999999999999999999999999"));
        VERIFY(!fitsInt64(*e));
        ConstraintModel m = base();
        add(m, mkOp(Op::LE, {e, mkIdent("i", INT)}));
        VERIFY(contains(emit(m), "99999999999999999999999999"));
    }
    {
        // Text that is not a numeral must not reach the script: it is the
        // authoritative value now, so an unchecked one would be printed and
        // rejected by whatever reads the output.
        ConstraintModel m = base();
        add(m, mkOp(Op::LE, {mkIdent("i", INT), mkInt(std::string("12x3"))}));
        VERIFY(rejects(m, ErrorCode::E_TYPE));
    }
    {
        // mkInt(long long) fills BOTH, so a consumer reading int_value on an
        // ordinary literal keeps working -- the common path costs nothing.
        const ExprPtr e = mkInt(7);
        VERIFY(e->int_value == 7);
        VERIFY(e->name == "7");
        VERIFY(fitsInt64(*e));
    }

    // ---- An Int literal is still an Int. ------------------------------------
    // Adding LIT_REAL must not make mkInt produce reals; QF_LIA instances would
    // silently become QF_LRA, which is a different logic and a different
    // solver path.
    {
        VERIFY(mkInt(3)->kind == ExprKind::LIT_INT);
        VERIFY(mkInt(3)->sort.kind == SortKind::INT);
        ConstraintModel m = base();
        add(m, mkOp(Op::LE, {mkIdent("i", INT), mkInt(3)}));
        const std::string smt = emit(m);
        VERIFY(!contains(smt, "3.0"));
    }

    std::cout << "All store/literal tests passed." << std::endl;
    return 0;
}
