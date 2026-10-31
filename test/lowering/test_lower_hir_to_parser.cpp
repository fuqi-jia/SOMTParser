// Lowering assumes the HIR is feature-free: every construct maps one-to-one.
// parser.h must come before <cassert> because Parser::assert is a member
// function and parser.h undefines the macro.
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"
#include "translation/bound_semantics.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

static bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

int main() {
    // Sort is ambiguous unqualified: SOMTParser::Sort (the existing frontend
    // class) and SOMTParser::Uir::Hir::Sort are both in scope via the
    // using-directives above, so it needs the Hir:: qualifier. Model was
    // renamed to ConstraintModel precisely to remove the same ambiguity it
    // used to have with SOMTParser::Model -- a solver assignment, not a
    // problem specification -- so unlike Sort (the same concept at a
    // different layer, kept qualified on purpose) it no longer needs
    // disambiguating. The Hir:: qualifier is kept here anyway for
    // consistency with Sort.

    // (declare-const x Int) (assert (> (+ x 3) 0))
    Hir::ConstraintModel m;
    VarDecl dx;
    dx.name = "x";
    dx.sort = Hir::Sort::integer();
    m.decls.push_back(dx);

    VarDecl db;
    db.name = "b";
    db.sort = Hir::Sort::boolean();
    m.decls.push_back(db);

    Constraint c;
    c.formula = mkOp(Op::GT,
                     {mkOp(Op::ADD, {mkIdent("x", Hir::Sort::integer()), mkInt(3)}),
                      mkInt(0)});
    m.constraints.push_back(c);

    Constraint c2;
    c2.formula = mkOp(Op::OR, {mkIdent("b", Hir::Sort::boolean()),
                               mkOp(Op::NOT, {mkIdent("b", Hir::Sort::boolean())})});
    m.constraints.push_back(c2);

    ParserPtr p = newParser();
    Lower::HirToParser lowerer(p);
    TranslationReport report;
    Diagnostics diags;
    const bool ok = lowerer.lower(m, report, diags);
    assert(ok);
    assert(!diags.hasErrors());

    // Both variables were declared and are reachable by name.
    assert(lowerer.varMap().size() == 2);
    assert(lowerer.varMap().count("x") == 1);
    assert(lowerer.varMap().count("b") == 1);

    // Both constraints reached the parser.
    assert(p->getAssertions().size() == 2);

    // Stats feed the evaluation database.
    assert(report.stats().num_vars == 2);
    assert(report.stats().num_constraints == 2);

    // The dump must mention the declarations. Builders fold and reorder, so
    // assert on the presence of symbols, never on an exact string.
    const std::string smt = p->dumpSMT2();
    assert(contains(smt, "x"));
    assert(contains(smt, "b"));
    assert(contains(smt, "Int"));

    // An unknown identifier is a reported error, not a crash or a silent zero.
    {
        Hir::ConstraintModel bad;
        Constraint bc;
        bc.formula = mkOp(Op::GT, {mkIdent("undeclared", Hir::Sort::integer()), mkInt(0)});
        bad.constraints.push_back(bc);
        ParserPtr p2 = newParser();
        Lower::HirToParser l2(p2);
        TranslationReport r2;
        Diagnostics d2;
        assert(!l2.lower(bad, r2, d2));
        assert(d2.hasErrors());
        assert(d2.firstErrorCode() == ErrorCode::E_INTERNAL);
    }

    // Variable bounds become ordinary assertions -- and in the right
    // direction. The count alone cannot see that: swapping mkGe/mkLe in
    // HirToParser::lower emits "y <= 1 and y >= 9", which is trivially UNSAT,
    // yet keeps this count, every fidelity flag and every recorded Bound
    // exactly as they are. Read the meaning of each assertion instead.
    {
        Hir::ConstraintModel bounded;
        VarDecl d;
        d.name = "y";
        d.sort = Hir::Sort::integer();
        d.lower_bound = mkInt(1);
        d.upper_bound = mkInt(9);
        bounded.decls.push_back(d);
        ParserPtr p3 = newParser();
        Lower::HirToParser l3(p3);
        TranslationReport r3;
        Diagnostics d3;
        assert(l3.lower(bounded, r3, d3));

        const auto asserts = p3->getAssertions();
        assert(asserts.size() == 2);
        // Both assertions are readable as a bound on "y", so neither escapes
        // the two content checks below by being an unrecognised shape.
        const auto bounds = test_bounds::varBoundsOf(asserts);
        assert(bounds.size() == 2);
        // The lower bound constrains y from below, the upper from above.
        assert(test_bounds::hasVarBound(asserts, "y", test_bounds::Rel::GE, "1"));
        assert(test_bounds::hasVarBound(asserts, "y", test_bounds::Rel::LE, "9"));
        // ...and not the reverse, which is what a swapped mkGe/mkLe emits.
        assert(!test_bounds::hasVarBound(asserts, "y", test_bounds::Rel::LE, "1"));
        assert(!test_bounds::hasVarBound(asserts, "y", test_bounds::Rel::GE, "9"));
    }

    // A soft constraint is refused, never silently hardened. parser_->assert()
    // would drop the weight and the group and turn "violate at cost w" into
    // "never violate", which can report UNSAT for a satisfiable MaxSMT
    // instance -- a wrong answer dressed up as a successful translation.
    {
        Hir::ConstraintModel softm;
        VarDecl d;
        d.name = "s";
        d.sort = Hir::Sort::boolean();
        softm.decls.push_back(d);
        Constraint sc;
        sc.formula = mkIdent("s", Hir::Sort::boolean());
        sc.soft = true;
        sc.weight = 7.5;
        sc.group = "prefs";
        softm.constraints.push_back(sc);

        ParserPtr p4 = newParser();
        Lower::HirToParser l4(p4);
        TranslationReport r4;
        Diagnostics d4;
        // This used to assert the REFUSAL: there was no public builder for a
        // soft assertion, and hardening one would have changed the problem from
        // "violate this at cost w" to "never violate this", which can turn a
        // satisfiable MaxSMT instance UNSAT. Parser::assertSoft landed on
        // 2026-08-12, so the scaffold goes and the assertion inverts -- the same
        // lifecycle as the decomposition pass's.
        assert(l4.lower(softm, r4, d4));
        assert(!d4.hasErrors());

        // The property the refusal was protecting: it did NOT become a hard
        // assertion. That is the assertion that must survive the inversion --
        // "it lowered" alone would pass for a frontend that hardened it.
        assert(p4->getAssertions().empty());

        const std::string smt = p4->dumpSMT2();
        assert(contains(smt, "assert-soft"));
        assert(contains(smt, ":id prefs"));
        // MaxSMT keeps a fractional weight exact. The internal rational 15/2
        // must be emitted as the solver's decimal token 7.5, not rounded to 7
        // or printed as an unsupported slash token.
        assert(contains(smt, ":weight 7.5"));
        assert(!contains(smt, ":weight 7)"));

        // ...and the dumped script is one this library reads back, which is
        // what makes the soft assertion survive the round trip at all: before
        // this, dumpSMT2 emitted nothing for it and a MaxSAT problem came back
        // as a plain SAT problem.
        ParserPtr reread = newParser();
        assert(reread->parseStr(smt));
        assert(!reread->dumpSMT2().empty());
        assert(contains(reread->dumpSMT2(), "assert-soft"));
    }
    {
        // An integral weight is emitted as an integer, not as `3.0`: SMT-LIB
        // takes a numeral and the two spellings are different sorts.
        Hir::ConstraintModel m;
        VarDecl d;
        d.name = "s";
        d.sort = Hir::Sort::boolean();
        m.decls.push_back(d);
        Constraint sc;
        sc.formula = mkIdent("s", Hir::Sort::boolean());
        sc.soft = true;
        sc.weight = 3.0;
        m.constraints.push_back(sc);

        ParserPtr p = newParser();
        Lower::HirToParser l(p);
        TranslationReport r;
        Diagnostics d2;
        assert(l.lower(m, r, d2));
        const std::string smt = p->dumpSMT2();
        assert(contains(smt, ":weight 3"));
        assert(!contains(smt, "3.0"));
        // No :id when the group is empty, rather than an empty one.
        assert(!contains(smt, ":id"));
    }

    // num_vars must match the script that was emitted.
    //
    // It was model.decls.size(), so a model declaring the same name twice
    // reported two variables while emitting one declare-fun -- and num_vars is
    // a column in the experiment's own results table, where a size that does
    // not match the model a solver reads is worse than no size at all.
    // Uir::Hir::typeCheck now rejects a duplicate declaration before it can
    // reach translate()'s lowering step, but lower() is public API and this is
    // the layer whose number is being reported, so the property is pinned here
    // rather than left to depend on a check in a different file.
    {
        Hir::ConstraintModel dup;
        VarDecl a;
        a.name = "x";
        a.sort = Hir::Sort::integer();
        dup.decls.push_back(a);
        dup.decls.push_back(a);

        VarDecl b;
        b.name = "y";
        b.sort = Hir::Sort::integer();
        dup.decls.push_back(b);

        ParserPtr p5 = newParser();
        Lower::HirToParser l5(p5);
        TranslationReport r5;
        Diagnostics d5;
        assert(l5.lower(dup, r5, d5));
        assert(dup.decls.size() == 3);
        assert(l5.varMap().size() == 2);
        assert(r5.stats().num_vars == 2);
    }

    std::cout << "All HirToParser tests passed." << std::endl;
    return 0;
}
