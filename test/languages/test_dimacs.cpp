// The DIMACS CNF frontend, and the three obligations docs/languages/dimacs-cnf.md
// wrote down before it existed.
//
// The cross-format half -- DIMACS, QDIMACS and QCIR defining "the file's
// vocabulary" three different ways -- lives in
// test/languages/test_sat_cross_format.cpp.
//
// Two of the three obligations are about *not* losing something the file did not
// say out loud:
//
//   * a variable in 1..VARIABLES occurring in no clause is still a variable of
//     the problem, because the vocabulary is the header's;
//   * the empty clause is `false`, and mkOp(OR, {}) throws rather than producing
//     it -- a construction trap rather than a semantic gap, and one that would
//     be filed under the wrong failure bucket if it escaped.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/dimacs.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation run(const std::string& src, bool strict = false) {
    Lang::SourceUnit u;
    u.main_path = "t.cnf";
    u.display_name = "t.cnf";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "dimacs";
    opts.parse.strict = strict;
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "dimacs";
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
    std::cout << "======= DIMACS CNF frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* d = Lang::LanguageRegistry::instance().byId("dimacs");
    assert(d != nullptr);
    assert(d->extensions().size() == 2);

    // ---- A plain instance. --------------------------------------------------
    {
        const Translation t = runFile("languages/dimacs/instances/ok/simple.cnf");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun x1"));
        assert(has(smt, "or"));
        assert(has(smt, "not"));
        // §3: one Constraint PER CLAUSE. The implicit conjunction over
        // ConstraintModel::constraints is exactly right here, unlike QDIMACS
        // where a prefix must scope over the whole matrix and the model
        // therefore holds one constraint (qdimacs.md §4.2).
        assert(t.report().stats().num_constraints == 2);
        assert(t.report().stats().num_vars == 3);
        // No quantifiers: the negative control for the QBF arms' depth column.
        assert(t.report().stats().max_quantifier_alternations == 0);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Obligation 1: the vocabulary is the HEADER's. ----------------------
    // Variable 3 occurs in no clause and is still a variable of the problem --
    // unconstrained, not absent. Reporting two variables for a three-variable
    // file would understate the instance, and num_vars is a column in the
    // experiment's own results table.
    {
        const Translation t =
            runFile("languages/dimacs/instances/ok/unused_variable.cnf");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun x3"));
        assert(t.report().stats().num_vars == 3);
        assert(t.report().stats().num_constraints == 1);
    }
    {
        // ...and the converse -- a clause variable the header does not cover --
        // is a WARNING and the variable is kept. dimacs-cnf.md §4.2 draws the
        // asymmetry: an over-large VARIABLES is harmless, an over-small CLAUSES
        // is not, and an under-counting VARIABLES loses nothing because the
        // content declares the variable anyway.
        const Translation t = run("p cnf 2 1\n1 -5 0\n");
        assert(t.ok());
        assert(warns(t, "index 5"));
        assert(has(t.toSmt2(), "declare-fun x5"));
        assert(t.report().stats().num_vars == 5);
    }

    // ---- Obligation 2: the empty clause is false. ---------------------------
    // A construction trap and not a semantic gap. mkOp(Op::OR, {}) throws --
    // condAssert survives -DNDEBUG -- so an unhandled empty clause on this legal
    // input would surface as E_INTERNAL, under the bucket reserved for broken
    // invariants rather than for input.
    {
        const Translation t = runFile("languages/dimacs/instances/ok/empty_clause.cnf");
        assert(t.ok());
        assert(t.diagnostics().firstErrorCode() != ErrorCode::E_INTERNAL);
        assert(has(t.toSmt2(), "false"));
        assert(t.report().stats().num_constraints == 2);
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // No clauses at all is the opposite polarity and must not be confused
        // with it: an empty CNF is trivially satisfiable. The variables are
        // still declared, because the vocabulary is the header's.
        const Translation t = runFile("languages/dimacs/instances/ok/no_clauses.cnf");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 0);
        assert(t.report().stats().num_vars == 3);
        assert(!has(t.toSmt2(), "false"));
    }

    // ---- Obligation 3: no objective means vacuously true, not verified. -----
    // A statement about how the fidelity is READ rather than about the code, so
    // what is checkable is that nothing invents an objective.
    {
        const Translation t = runFile("languages/dimacs/instances/ok/simple.cnf");
        assert(t.ok());
        assert(t.report().stats().num_objectives == 0);
        assert(!has(t.toSmt2(), "minimize"));
        assert(!has(t.toSmt2(), "maximize"));
    }

    // ---- A clause may span lines. -------------------------------------------
    {
        const Translation t =
            runFile("languages/dimacs/instances/ok/multiline_clause.cnf");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 1);
        assert(t.report().stats().num_vars == 4);
    }

    // ---- §4.2: the mismatch policy, both branches. --------------------------
    {
        const Translation t = run("p cnf 2 7\n1 0\n-2 0\n");
        assert(t.ok());
        assert(warns(t, "7 clauses"));
        // The content won: both clauses are there.
        assert(t.report().stats().num_constraints == 2);
    }
    {
        // Trusting the header would stop after C clauses and drop the rest --
        // sound = false, a wrong answer reported as success. Three clauses
        // present, one declared: all three must survive.
        const Translation t = run("p cnf 2 1\n1 0\n-2 0\n1 2 0\n");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 3);
    }
    {
        // Under ParseOptions::strict the same file is refused, which is the
        // policy dimacs-cnf.md §4.2 offers at the cost of corpus coverage. The
        // point is that it is the caller's choice and not a difference the two
        // paths hide.
        const Translation t = run("p cnf 2 7\n1 0\n-2 0\n", /*strict=*/true);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    // ---- Malformed files. ---------------------------------------------------
    {
        const Translation t =
            runFile("languages/dimacs/instances/reject/no_problem_line.cnf");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "problem line"));
    }
    {
        const Translation t = runFile("languages/dimacs/instances/reject/unterminated.cnf");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "terminated"));
    }
    {
        const Translation t = runFile("languages/dimacs/instances/reject/junk_literal.cnf");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        // An oversized literal is E_PARSE with a line, not E_INTERNAL.
        const Translation t = run("p cnf 1 1\n99999999999999999999 0\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        const Translation t = runFile("languages/dimacs/instances/nosuch.cnf");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    std::cout << "All DIMACS tests passed." << std::endl;
    return 0;
}
