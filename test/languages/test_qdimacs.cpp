// QDIMACS 1.1: prefix dependencies, implicit closure, and whole-matrix scope.
//
// The cross-format half -- QDIMACS bound variables versus QCIR free variables --
// lives in test/languages/test_sat_cross_format.cpp, because a property about
// two frontends belongs where both are visible rather than half in each.
//
// Two shapes here are worth naming before reading the file.
//
// **One constraint, not a list.** The prefix scopes over the WHOLE matrix, so
// the model holds one Constraint whose formula is `∀… ∃… (c₁ ∧ c₂ ∧ …)`. A
// frontend that emitted one Constraint per clause would wrap each clause in its
// own prefix, and that formula is not merely different -- it is usually much
// easier, so the arm would report an SMT solver doing well on a problem nobody
// posed (qdimacs.md §4.2).
//
// **Alternation depth is the measurement.** The polynomial hierarchy's levels
// ARE alternation counts and QBF solvers are engineered against the prefix
// structure, so a result that does not stratify by it answers a question nobody
// asked (§4.3). It is reported in Stats now, and this file pins what it counts.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/qdimacs.h"
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

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0, at = 0;
    while ((at = hay.find(needle, at)) != std::string::npos) { ++n; at += needle.size(); }
    return n;
}

Translation run(const std::string& src, bool strict = false) {
    Lang::SourceUnit u;
    u.main_path = "t.qdimacs";
    u.display_name = "t.qdimacs";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "qdimacs";
    opts.parse.strict = strict;
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "qdimacs";
    return translate(u, opts);
}

bool warns(const Translation& t, const std::string& needle) {
    for (const auto& e : t.diagnostics().all()) {
        if (e.severity == Severity::WARNING && has(e.message, needle)) { return true; }
    }
    return false;
}


bool lifted(const Translation& t, const std::string& bound) {
    for (const auto& choice : t.report().choices()) {
        if (choice.strategy == "fresh-private-constant"
            && has(choice.rationale, "bound '" + bound + "' -> auxiliary '")) { return true; }
    }
    return false;
}

void privateOnly(const Translation& t, std::size_t witnesses) {
    const auto& stage = t.semantics().stages().back();
    assert(stage.source_signature.symbols.empty());
    assert(stage.projection.observables.empty());
    assert(stage.projection.optional_observables.empty());
    assert(stage.symbol_map.empty());
    assert(stage.target_signature.symbols.size() == witnesses);
    assert(t.report().stats().num_vars == witnesses);
}

} // namespace

int main() {
    std::cout << "======= QDIMACS 1.1 frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* q = Lang::LanguageRegistry::instance().byId("qdimacs");
    assert(q != nullptr);
    assert(q->extensions().size() == 1 && q->extensions()[0] == ".qdimacs");

    // ---- The document's own example. ----------------------------------------
    // forall x1 x2. exists x3 x4. (x1 | !x3) & (!x2 | x4)
    {
        const Translation t = runFile("languages/qdimacs/instances/ok/standard.qdimacs");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(forall "));
        assert(has(smt, "(exists "));
        // §2.2: the prefix's ORDER is the semantics. `∀x ∃y φ` and `∃y ∀x φ` are
        // different formulas with different answers -- the first lets y depend
        // on x, the second demands one y for every x. Both are well-formed.
        assert(smt.find("(forall ") < smt.find("(exists "));
        // §4.2: ONE constraint, with the prefix outside the whole conjunction.
        assert(t.report().stats().num_constraints == 1);
        // ...and no variable is declared: everything the matrix mentions is
        // bound, which is what §2.3's first row requires of a legal file.
        assert(!has(smt, "declare-fun"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- QDIMACS 1.1: unbound matrix atoms are outermost existential. ------
    {
        const Translation t =
            runFile("languages/qdimacs/instances/ok/free_variable.qdimacs");
        assert(t.ok());
        assert(has(t.toSmt2(), "declare-fun"));
        assert(lifted(t, "x2"));
        assert(count(t.toSmt2(), "(exists ") == 0);
        privateOnly(t, 2);
        assert(t.report().stats().max_quantifier_alternations == 0);
    }
    {
        // Plain DIMACS is legal QDIMACS, including in strict mode.
        const Translation t = run("p cnf 2 2\n1 -2 0\n-1 2 0\n", true);
        assert(t.ok());
        assert(count(t.toSmt2(), "(exists ") == 0);
        assert(lifted(t, "x1") && lifted(t, "x2"));
        privateOnly(t, 2);
    }
    {
        // x2 is fixed before universal x1, not chosen in the inner e block.
        // exists x2. forall x1. exists x3. (x1 iff x2) and x3 is false.
        const Translation t = run(
            "p cnf 3 3\na 1 0\ne 3 0\n-1 2 0\n1 -2 0\n3 0\n", true);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(lifted(t, "x2"));
        privateOnly(t, 1);
        assert(smt.find("(forall ") < smt.find("(exists "));
        assert(count(smt, "(exists ") == 1);
        // This metric describes the emitted formula after witness lifting.
        assert(t.report().stats().max_quantifier_alternations == 1);
        assert(t.report().stats().num_constraints == 1);
    }
    {
        // Repeated implicit occurrences introduce one private witness per binder.
        const Translation t = run("p cnf 2 1\ne 1 0\n2 -2 2 1 0\n", true);
        assert(t.ok());
        assert(count(t.toSmt2(), "(exists ") == 0);
        privateOnly(t, 2);
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }

    // ---- §2.3 row 2: a prefix variable in no clause still binds. ------------
    // It also still fixes the alternation depth, so dropping the unused blocks
    // would report a shallower instance than the file describes -- and depth is
    // the parameter the whole comparison is stratified by.
    {
        const Translation t =
            runFile("languages/qdimacs/instances/ok/unused_prefix_var.qdimacs");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "x1"));                 // quantified, in no clause
        assert(has(smt, "x3"));
        assert(!has(smt, "declare-fun"));       // bound, not free
        assert(t.report().stats().max_quantifier_alternations == 1);
    }

    // ---- §4.3: what alternation depth counts. -------------------------------
    {
        // Four blocks, alternating: three changes.
        const Translation t =
            runFile("languages/qdimacs/instances/ok/deep_alternation.qdimacs");
        assert(t.ok());
        assert(t.report().stats().max_quantifier_alternations == 3);
    }
    {
        // Two ADJACENT existential blocks after a universal: one alternation,
        // not two. §2.2 says adjacent same-quantifier blocks may be merged or
        // reordered freely, which is exactly what the hierarchy's levels count.
        // Counting blocks instead of changes would say 2 here and would make a
        // Σ₂ instance look like a Σ₃ one.
        const Translation t =
            runFile("languages/qdimacs/instances/ok/merged_blocks.qdimacs");
        assert(t.ok());
        assert(t.report().stats().max_quantifier_alternations == 1);
    }
    {
        // A single existential block is a plain SAT instance in QDIMACS
        // clothing -- qdimacs.md §4.3's negative control. Zero alternations.
        const Translation t = run("p cnf 2 1\ne 1 2 0\n1 -2 0\n");
        assert(t.ok());
        assert(t.report().stats().max_quantifier_alternations == 0);
        assert(!has(t.toSmt2(), "(exists "));
        privateOnly(t, 2);
    }
    {
        // A quantifier-free model reports zero, so the statistic does not
        // quietly count something else for the other twenty-two languages.
        const Translation t = run("p cnf 1 0\ne 1 0\n");
        assert(t.ok());
        assert(t.report().stats().max_quantifier_alternations == 0);
    }

    // ---- The empty clause and the empty matrix, opposite polarities. --------
    {
        // dimacs-cnf.md §4.1's trap. The empty clause is FALSE; the instance is
        // unsatisfiable, which is an answer and a legal file.
        const Translation t =
            runFile("languages/qdimacs/instances/ok/empty_clause.qdimacs");
        assert(t.ok());
        assert(has(t.toSmt2(), "false"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // No clauses at all: the empty conjunction is TRUE. Getting this pair
        // backwards turns every unsatisfiable instance satisfiable and back.
        const Translation t =
            runFile("languages/qdimacs/instances/ok/no_clauses.qdimacs");
        assert(t.ok());
        assert(has(t.toSmt2(), "true"));
    }

    // ---- §4.2: the p-line mismatch policy. ----------------------------------
    // Trust the content and WARN. Trusting the header would stop after C
    // clauses and silently drop the rest, making the translated problem weaker
    // -- a wrong answer reported as success.
    {
        const Translation t = run("p cnf 2 5\ne 1 2 0\n1 0\n-2 0\n");
        assert(t.ok());
        assert(warns(t, "5 clauses"));
        // Both clauses and their independently recorded binders survived.
        assert(lifted(t, "x1"));
        assert(lifted(t, "x2"));
    }
    {
        // An index beyond the declared count is warned about too, and the
        // variable is kept.
        const Translation t = run("p cnf 1 1\ne 1 7 0\n7 0\n");
        assert(t.ok());
        assert(warns(t, "index 7"));
        assert(lifted(t, "x7"));
    }
    {
        // Under ParseOptions::strict the same files are refused, which is the
        // policy dimacs-cnf.md §4.2 offers as "also defensible, at the cost of
        // corpus coverage". The point is that it is a *choice* the caller makes
        // and not a difference the two paths hide.
        const Translation t = run("p cnf 2 5\ne 1 2 0\n1 0\n-2 0\n", /*strict=*/true);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    // ---- What a malformed file must not get away with. ----------------------
    for (const std::string source : {
             "p cnf 1 1 junk\ne 1 0\n1 0\n",
             "p cnf 1 1\ne 1 0 -1 0\n1 0\n"}) {
        const Translation t = run(source);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "unexpected token"));
    }
    {
        const Translation t =
            runFile("languages/qdimacs/instances/reject/double_quantified.qdimacs");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "twice"));
    }
    {
        // The prefix precedes the matrix; a quantifier line after a clause would
        // silently change the nesting if it were accepted as a late block.
        const Translation t =
            runFile("languages/qdimacs/instances/reject/prefix_after_matrix.qdimacs");
        assert(!t.ok());
    }
    {
        const Translation t =
            runFile("languages/qdimacs/instances/reject/no_problem_line.qdimacs");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "problem line"));
    }
    {
        const Translation t =
            runFile("languages/qdimacs/instances/reject/unterminated_clause.qdimacs");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "terminated"));
    }
    {
        // A negated literal in a quantifier block: blocks list VARIABLES.
        const Translation t = run("p cnf 1 1\ne -1 0\n1 0\n");
        assert(!t.ok());
    }
    {
        // An unterminated quantifier block.
        const Translation t = run("p cnf 1 1\ne 1\n1 0\n");
        assert(!t.ok());
    }
    {
        // An integer literal too large for long long is an input problem with a
        // line number, not an exception escaping into the blanket handler where
        // it would be filed as E_INTERNAL -- the bucket reserved for broken
        // invariants.
        const Translation t = run("p cnf 1 1\ne 99999999999999999999 0\n1 0\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        // Its magnitude is not representable: reject before any llabs call.
        const Translation t = run("p cnf 1 1\n-9223372036854775808 0\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "not a literal"));
    }
    {
        const Translation t = runFile("languages/qdimacs/instances/nosuch.qdimacs");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- The whole matrix is inside the whole prefix. -----------------------
    // The failure §4.2 warns about is a frontend that lowers clause by clause
    // and wraps each one. Such a translation would produce as many `forall`s as
    // there are clauses; this asserts there is exactly one of each block.
    {
        const Translation t = run(
            "p cnf 3 3\na 1 0\ne 2 3 0\n1 2 0\n-1 3 0\n2 -3 0\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "(forall ") == 1);
        assert(count(smt, "(exists ") == 1);
        assert(t.report().stats().num_constraints == 1);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    std::cout << "All QDIMACS tests passed." << std::endl;
    return 0;
}
