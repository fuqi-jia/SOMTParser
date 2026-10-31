// The first real language: it must build, register, be detected, and translate.
#include "somtparser/languages/minizinc.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"
#include "somtparser/frontend/parser.h"
#include "translation/bound_semantics.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

static bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    Lang::Language* mzn = Lang::LanguageRegistry::instance().byId("minizinc");
    assert(mzn != nullptr);
    assert(mzn->extensions().size() >= 1);
    assert(mzn->extensions()[0] == ".mzn");

    // Declarations, a constraint and an objective.
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source =
            "% a comment\n"
            "var 0..10: x;\n"
            "var bool: b;\n"
            "constraint x + 3 > 0;\n"
            "constraint b \\/ not b;\n"
            "solve minimize x;\n";
        Translation t = translate(u);
        assert(t.ok());
        assert(t.report().provenance().language_id == "minizinc");

        // Two constraints plus the two domain bounds of x. The count says the
        // bounds arrived; only reading them says they arrived the right way
        // round. "var 0..10: x" must become x >= 0 and x <= 10 -- the swapped
        // form (x <= 0 and x >= 10) is UNSAT yet leaves this count, the stats
        // and the fidelity report identical.
        const auto asserts = t.parser()->getAssertions();
        assert(asserts.size() == 4);
        assert(test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::GE, "0"));
        assert(test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::LE, "10"));
        assert(!test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::LE, "0"));
        assert(!test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::GE, "10"));
        assert(t.report().stats().num_vars == 2);
        assert(t.report().stats().num_objectives == 1);

        const std::string s = t.toSmt2();
        assert(contains(s, "x"));
        assert(contains(s, "(define-objective"));
        assert(contains(s, "OBJECTIVE_MIN"));
    }

    // solve satisfy yields no objective.
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source = "var int: z;\nconstraint z = 4;\nsolve satisfy;\n";
        Translation t = translate(u);
        assert(t.ok());
        assert(t.report().stats().num_objectives == 0);
        assert(t.toSmt2().find("define-objective") == std::string::npos);
    }

    // Syntax errors are reported with a location, not thrown.
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source = "var int: ;\n";
        Translation t = translate(u);
        assert(!t.ok());
        assert(t.diagnostics().hasErrors());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(t.diagnostics().all()[0].loc.line == 1);
    }

    // MiniZinc floats denote real values. Decimal/scientific constants are
    // converted to exact rationals, not routed through double, and `/` retains
    // relational definedness at zero.
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source =
            "float: scale = 1.25e1;\n"
            "float: hex = 0x1.1p2;\n"
            "var float: x;\n"
            "var int: n;\n"
            "constraint x = scale / 2.0 + n;\n"
            "constraint x >= hex;\n"
            "constraint x > 0.5;\n"
            "solve minimize x;\n";
        Translation t = translate(u);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(contains(smt, "(declare-fun x () Real)"));
        assert(contains(smt, "25"));
        assert(contains(smt, "(/ 17 4)"));
        assert(contains(smt, "OBJECTIVE_MIN"));
    }
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source =
            "array[1..2] of var float: a;\n"
            "predicate positive(var float: v) = v > 0.0;\n"
            "constraint positive(a[1]);\n"
            "solve satisfy;\n";
        Translation t = translate(u);
        assert(t.ok());
        assert(contains(t.toSmt2(), "(Array Int Real)"));
    }

    // Fixed functions evaluate their body, rather than merely accepting the
    // declaration or replacing each call with an unconstrained value.
    for (int expected : {3, 4}) {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source =
            "function int: f(int: x) = x + 1;\n"
            "constraint f(3) = " + std::to_string(expected) + ";\n"
            "solve satisfy;\n";
        Translation t = translate(u);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(contains(smt, "(assert false)") == (expected == 3));
        assert(contains(smt, "(assert true)") == (expected == 4));
    }
    {
        // And the construct that used to stand here now translates, which is
        // the other half of the claim: the example moved because the gap
        // closed, not because the assertion was weakened.
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source = "set of int: s = {1};\nsolve satisfy;\n";
        Translation t = translate(u);
        assert(t.ok());
    }

    // ...and an array declaration now translates.
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source = "array[1..3] of var int: a;\nsolve satisfy;\n";
        Translation t = translate(u);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(smt.find("(Array Int Int)") != std::string::npos);
    }

    // Using an undeclared identifier is a type error, caught in the frontend.
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source = "constraint q > 0;\nsolve satisfy;\n";
        Translation t = translate(u);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    // A .dzn data file is READ, and a missing one is reported by name.
    //
    // This used to assert the opposite: MiniZincLanguage did not override
    // acceptsDataFiles(), so translate() refused any unit carrying one rather
    // than parse the .mzn alone and report success for a model whose data never
    // arrived. That guard was right for a frontend that could not read data and
    // is the wrong answer for one that can -- the risk it was protecting
    // against (data silently dropped) is now impossible for a different reason.
    // What must not regress is that a data file which cannot be read STOPS the
    // translation instead of being passed over.
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source = "var int: x;\nconstraint x > 0;\nsolve satisfy;\n";
        u.data_paths = {"t.dzn"};
        Translation t = translate(u);
        assert(!t.ok());
        assert(t.diagnostics().hasErrors());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
        assert(contains(t.diagnostics().all()[0].message, "t.dzn"));
        assert(t.parser() == nullptr);
    }

    // The identical translation without the data path still succeeds, so what
    // fails above is the dropped data file and not the model.
    {
        Lang::SourceUnit u;
        u.main_path = "t.mzn";
        u.inline_source = "var int: x;\nconstraint x > 0;\nsolve satisfy;\n";
        Translation t = translate(u);
        assert(t.ok());
        assert(!t.diagnostics().hasErrors());
    }

    // The bundled fixtures behave as their directory promises.
    {
        Lang::SourceUnit ok;
        ok.main_path = "languages/minizinc/instances/ok/trivial.mzn";
        assert(translate(ok).ok());

        Lang::SourceUnit real;
        real.main_path = "languages/minizinc/instances/ok/float_exact.mzn";
        const Translation rt = translate(real);
        assert(rt.ok());
        const std::string smt = rt.toSmt2();
        // 1.25e1 / 2.0 is the exact rational 25/4.
        assert(contains(smt, "(/ 25 4)"));
        // denominator=0 is legal because the division occurs only in the
        // false consequent's Boolean scope; the guard must stay under `=>`.
        assert(contains(smt, "(=> use_ratio (and"));
        assert(contains(smt, "(distinct 0.0 denominator)"));

        Lang::SourceUnit bad;
        bad.main_path = "languages/minizinc/instances/reject/bad_syntax.mzn";
        assert(!translate(bad).ok());
    }

    std::cout << "All minimal MiniZinc tests passed." << std::endl;
    return 0;
}
