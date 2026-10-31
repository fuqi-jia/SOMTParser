// The MPS frontend, and the six obligations docs/languages/mps.md wrote down
// before it existed.
//
// Three of them are about things that are MARKERS rather than data -- state a
// reader carries between lines, invisible in any single one, and therefore
// invisible to a reviewer reading a line at a time:
//
//   * `MARKER 'INTORG'` / `'INTEND'` bracket the INTEGER columns. Ignoring them
//     makes every variable continuous, which is the LP RELAXATION: complete =
//     true, sound = false, and a strictly easier and different problem whose
//     optimum gets reported as this one's.
//   * The FIRST `N` row is the objective; later ones are free rows constraining
//     nothing. Reading a second `N` row as a constraint invents one.
//   * A `RANGES` entry on an `E` row stops it being an equality, and which side
//     the interval extends to is decided by the SIGN of the range value. Taking
//     the absolute value gives the wrong interval on half the instances.
//
// One is a genuine divergence between readers rather than a rule -- `BOUNDS UP`
// with a negative value, where CPLEX has a third behaviour at exactly `UP 0` --
// so the rule taken is warned per instance rather than assumed.
//
// The remaining two are LP's, inherited: a column with no `BOUNDS` entry is
// non-negative, and `BV` is integer and {0,1} overriding anything else.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/mps.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/omt_emitter.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.mps";
    u.display_name = "t.mps";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "mps";
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "mps";
    return translate(u, opts);
}

bool warns(const Translation& t, const std::string& needle) {
    for (const auto& e : t.diagnostics().all()) {
        if (e.severity == Severity::WARNING && has(e.message, needle)) { return true; }
    }
    return false;
}

} // namespace

int main() {
    std::cout << "======= MPS frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* m = Lang::LanguageRegistry::instance().byId("mps");
    assert(m != nullptr);
    assert(m->extensions().size() == 1 && m->extensions()[0] == ".mps");

    // ---- The document's own example. ----------------------------------------
    {
        const Translation t = runFile("languages/mps/instances/ok/doc_example.mps");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // XONE is inside the INTORG bracket and YTWO is not.
        assert(has(smt, "declare-fun XONE () Int"));
        assert(has(smt, "declare-fun YTWO () Real"));
        // LIM1 is `L` with rhs 4 and range 2.5, so [4 - 2.5, 4] = [1.5, 4], and
        // 1.5 is exact: (/ 3 2), not 1.5000000000000002.
        assert(has(smt, "(/ 3 2)"));
        assert(has(smt, "OBJECTIVE_MIN"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
    }

    // ---- Obligation: MARKER lines are positional state. ---------------------
    // Ignoring them makes every variable continuous -- the LP relaxation, which
    // is a different and strictly easier problem. The fixture has two integer
    // columns inside the bracket and one continuous column after it, so a
    // frontend that drops the markers, or that never closes the bracket, is
    // caught either way.
    {
        const Translation t = runFile("languages/mps/instances/ok/integer_markers.mps");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun I1 () Int"));
        assert(has(smt, "declare-fun I2 () Int"));
        assert(has(smt, "declare-fun C1 () Real"));
        // With no selected BOUNDS record, marker integers use CPLEX's 0/1
        // default. Omitting these upper bounds changes a binary MIP to a
        // general-integer one.
        assert(has(smt, "(<= I1 1)"));
        assert(has(smt, "(<= I2 1)"));
    }

    // ---- Obligation: only the first N row is the objective. -----------------
    {
        const Translation t = runFile("languages/mps/instances/ok/second_n_row.mps");
        assert(t.ok());
        // One objective, not two, and no constraint invented from the free row.
        assert(t.report().stats().num_objectives == 1);
        assert(t.report().stats().num_constraints == 1);
        // The convention is not universal, so the choice is said out loud.
        assert(warns(t, "second N row"));
        // The free row's coefficient does not appear in the objective: 5.0 was
        // FREEROW's, and COST's is 1.
        assert(!has(t.toSmt2(), "5"));
    }

    // ---- Obligation: RANGES on an E row, and the sign decides the side. -----
    // The same row with +3 and -3 gives [10,13] and [7,10]. Taking |R| would
    // give [10,13] for both, which is wrong on exactly half the instances and
    // wrong in the permissive direction on neither -- it is simply a different
    // problem.
    {
        const Translation pos =
            runFile("languages/mps/instances/ok/ranges_e_positive.mps");
        const Translation neg =
            runFile("languages/mps/instances/ok/ranges_e_negative.mps");
        assert(pos.ok() && neg.ok());
        const std::string ps = pos.toSmt2();
        const std::string ns = neg.toSmt2();
        assert(has(ps, "13"));
        assert(!has(ps, " 7)"));
        assert(has(ns, " 7"));
        assert(!has(ns, "13"));
        // And neither is an equality any more.
        assert(!has(ps, "(= "));
        assert(!has(ns, "(= "));
    }
    {
        // L and G rows use |R| on the side their operator leaves open, which is
        // the part that does NOT depend on the sign -- so a frontend that made
        // every row sign-sensitive would break these.
        const Translation l = run(
            "ROWS\n N  C\n L  R\nCOLUMNS\n    X         C            1.0        R"
            "            1.0\nRHS\n    R1        R            10.0\nRANGES\n"
            "    RG        R            -3.0\nENDATA\n");
        assert(l.ok());
        // L with rhs 10 and |R| = 3 is [7, 10] whatever the sign.
        assert(has(l.toSmt2(), " 7"));
        assert(has(l.toSmt2(), "10"));
    }

    // ---- BOUNDS types. ------------------------------------------------------
    {
        const Translation t = runFile("languages/mps/instances/ok/bounds_types.mps");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // BV: integer and {0,1}.
        assert(has(smt, "declare-fun B () Int"));
        assert(has(smt, "(>= B 0.0)"));
        assert(has(smt, "(<= B 1.0)"));
        // FR: neither bound.
        assert(!has(smt, "(>= F 0)") && !has(smt, "(>= F 0.0)"));
        // MI: the lower bound is opened, so the default 0 must NOT appear.
        assert(!has(smt, "(>= M 0)") && !has(smt, "(>= M 0.0)"));
        // FX: both bounds at 7.
        assert(has(smt, "(>= X 7.0)"));
        assert(has(smt, "(<= X 7.0)"));
        // D has no BOUNDS entry at all and is still non-negative, which no line
        // of the file says.
        assert(has(smt, "(>= D 0)"));
    }

    // ---- The UP divergence is warned, not assumed. --------------------------
    {
        const Translation t = runFile("languages/mps/instances/ok/up_negative.mps");
        assert(t.ok());
        assert(warns(t, "UP with a negative value"));
        const std::string smt = t.toSmt2();
        assert(has(smt, "(- 3.0)"));
        // The lower bound was opened, so the default 0 is gone -- otherwise the
        // model would be `0 <= X <= -3`, infeasible, which is the reading the
        // warning exists to say was NOT taken.
        assert(!has(smt, "(>= X 0)") && !has(smt, "(>= X 0.0)"));
    }
    {
        // `UP 0` is CPLEX's third behaviour: the lower bound STAYS at 0, fixing
        // the variable. A rule written as "negative upper bound opens the lower
        // one" gets this right only if zero is not counted as negative.
        const Translation t = run(
            "ROWS\n N  C\n L  R\nCOLUMNS\n    X         C            1.0        R"
            "            1.0\nBOUNDS\n UP BND       X            0.0\nENDATA\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(>= X 0)"));
        assert(has(smt, "(<= X 0.0)"));
        assert(!warns(t, "UP with a negative value"));
    }
    {
        // `-0.0` is zero, and the rule is "STRICTLY less than 0". Testing the
        // first character instead of the value calls this negative and opens
        // the lower bound on a file that meant to fix the variable at zero --
        // the same boundary CPLEX treats as its own case, reached by a
        // different spelling.
        const Translation t = run(
            "ROWS\n N  C\n L  R\nCOLUMNS\n    X         C            1.0        R"
            "            1.0\nBOUNDS\n UP BND       X            -0.0\nENDATA\n");
        assert(t.ok());
        assert(!warns(t, "UP with a negative value"));
        assert(has(t.toSmt2(), "(>= X 0)"));
    }

    // ---- OBJSENSE. ----------------------------------------------------------
    {
        const Translation t = run(
            "OBJSENSE\n    MAX\nROWS\n N  C\n G  R\nCOLUMNS\n    X         C"
            "            1.0        R            1.0\nENDATA\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "OBJECTIVE_MAX"));
    }
    {
        // Absent means minimise.
        const Translation t = run(
            "ROWS\n N  C\n G  R\nCOLUMNS\n    X         C            1.0        R"
            "            1.0\nENDATA\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "OBJECTIVE_MIN"));
    }
    {
        // OBJNAME can select a later N row. Without it the first N row is the
        // objective and the other is discarded.
        const Translation t = run(
            "NAME OBJSEL\nOBJNAME\n    SECOND\nROWS\n N FIRST\n N SECOND\n"
            " L LIMIT\nCOLUMNS\n    X FIRST 1 SECOND 5\n    X LIMIT 1\n"
            "RHS\n    RHS LIMIT 2\nENDATA\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(* 5.0 X)") || has(t.toSmt2(), "(* X 5.0)"));
        assert(warns(t, "OBJNAME"));
    }
    {
        // RHS on the objective row stores the negative objective offset.
        // Consequently -3.5 in MPS contributes +3.5 to the OMT term.
        const Translation t = run(
            "NAME OFFSET\nROWS\n N OBJ\n G R\nCOLUMNS\n    X OBJ 1 R 1\n"
            "RHS\n    RHS OBJ -3.5 R 0\nENDATA\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(/ 7 2)"));
    }
    {
        // Only the first named vector in each optional data family is selected.
        // Later vectors must not overwrite the active RHS or bounds.
        const Translation t = run(
            "NAME VECTORS\nROWS\n N OBJ\n E R\nCOLUMNS\n    X OBJ 1 R 1\n"
            "RHS\n    FIRST R 2\n    SECOND R 9\nBOUNDS\n"
            " UP B1 X 3\n UP B2 X 8\nENDATA\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, " 2") && has(smt, " 3"));
        assert(!has(smt, " 9") && !has(smt, " 8"));
    }
    {
        // A marker integer with no bound record defaults to binary, but an
        // explicit PL record requests the ordinary unbounded integer upper end.
        const Translation t = run(
            "NAME GENERALINT\nROWS\n N OBJ\n G R\nCOLUMNS\n"
            "    M 'MARKER' 'INTORG'\n    X OBJ 1 R 1\n    M 'MARKER' 'INTEND'\n"
            "RHS\n    RHS R 0\nBOUNDS\n PL BND X\nENDATA\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "declare-fun X () Int"));
        assert(!has(t.toSmt2(), "(<= X 1)"));
    }
    {
        // SC defaults its positive semi-continuous lower bound to 1 in MPS.
        // The LP section has a different default, so this belongs in the
        // per-language assumption profile rather than a shared syntax rule.
        const Translation t = run(
            "NAME SCDEFAULT\nROWS\n N OBJ\n E R\nCOLUMNS\n    X OBJ 1 R 1\n"
            "RHS\n    RHS R .5\nBOUNDS\n SC BND X 10\nENDATA\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(or") && has(smt, " 1") && has(smt, "10"));
    }
    {
        // HiGHS/Xpress SI is the semi-integer counterpart of SC.
        const Translation t =
            runFile("languages/mps/instances/upstream/semi-integer.mps");
        assert(t.ok());
        assert(has(t.toSmt2(), "declare-fun x3 () Int"));
        assert(has(t.toSmt2(), "(or"));
    }

    // ---- Scientific notation is legal MPS and is not an SMT-LIB numeral. ----
    {
        const Translation t = run(
            "ROWS\n N  C\n L  R\nCOLUMNS\n    X         C            1.0        R"
            "            1.5e2\nRHS\n    R1        R            1e-3\nENDATA\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Expanded as text, so it stays exact: 150 and one thousandth.
        assert(has(smt, "150"));
        assert(has(smt, "(/ 1 1000)"));
        // The literals themselves are gone, rather than "no letter e anywhere"
        // -- `declare-fun` and `set-logic` have one, and the first draft of this
        // line asserted against those too.
        assert(!has(smt, "1.5e2"));
        assert(!has(smt, "1e-3"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
    }

    // ---- Malformed and unsupported. ----------------------------------------
    {
        const Translation t = runFile("languages/mps/instances/reject/no_rows.mps");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "ROWS"));
    }
    {
        const Translation t =
            runFile("languages/mps/instances/reject/undeclared_row.mps");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        // SOS is a coverage gap and not a parse error: the file is valid MPS.
        const Translation t = runFile("languages/mps/instances/reject/sos_section.mps");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        Lang::Language* mps = Lang::LanguageRegistry::instance().byId("mps");
        assert(mps->coverage().missing.size() == 3);
    }
    {
        const Translation duplicate = run(
            "NAME DUPBOUND\nROWS\n N OBJ\nCOLUMNS\n    X OBJ 1\nBOUNDS\n"
            " LO BND X 0\n LO BND X 1\nENDATA\n");
        assert(!duplicate.ok());
        assert(duplicate.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);

        const Translation unknown = run(
            "NAME UNKNOWN\nROWS\n N OBJ\nCOLUMNS\n    X OBJ 1\nNETWORK\nENDATA\n");
        assert(!unknown.ok());
        assert(unknown.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }
    {
        const Translation t = runFile("languages/mps/instances/nosuch.mps");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    std::cout << "All MPS tests passed." << std::endl;
    return 0;
}
