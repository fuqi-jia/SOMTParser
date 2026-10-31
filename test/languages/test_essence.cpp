// The Essence' frontend, and the four obligations docs/languages/essence-prime.md
// wrote down before it existed. None of them is written in any line of a model.
//
//   1. **A sparse domain is a SET.** `int(1, 3, 5)` is not `int(1..5)`. The
//      HIR's VarDecl carries a lower and an upper bound and nothing else, so a
//      sparse domain must also emit a membership constraint -- without it the
//      model admits 2 and 4, a strictly larger solution set than the one
//      written, and every extra solution type-checks.
//   2. **A matrix index must lie in its declared index domain.** SMT-LIB arrays
//      are total, so `q[0]` on a matrix indexed by `int(1..n)` reads a value the
//      model never declared and the solver is free to choose it.
//   3. **A quantifier is EXPANDED against the parameter.** Its range is a
//      materialised set, so the quantifier has no meaning until the .param file
//      is known -- which is also why a parameter with no value is refused
//      rather than defaulted.
//   4. **A `where` clause constrains the PARAMETERS, not the model.** Lowered
//      as a constraint it would let a solver satisfy the model by choosing
//      parameter values that are not its to choose.

#include "distinct_scope.h"
#include "somtparser/translation/translate.h"
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
    std::size_t n = 0, p = 0;
    while ((p = hay.find(needle, p)) != std::string::npos) { ++n; p += needle.size(); }
    return n;
}

Translation runFile(const std::string& path, const std::string& param = "",
                    const std::string& profile = "") {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    if (!param.empty()) { u.data_paths.push_back(param); }
    TranslateOptions opts;
    opts.language_id = "essence";
    if (!profile.empty()) { opts.profile_id = profile; }
    return translate(u, opts);
}

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.eprime";
    u.display_name = "t.eprime";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "essence";
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= Essence' frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* e = Lang::LanguageRegistry::instance().byId("essence");
    assert(e != nullptr);
    assert(e->extensions().size() == 1 && e->extensions()[0] == ".eprime");
    // Without this, translate() refuses a unit carrying data files outright --
    // which is the guard that stops a frontend silently translating the model
    // alone and reporting success on a problem it never fully read.
    assert(e->acceptsDataFiles());

    // The language declaration ends at its newline. A stray statement on the
    // next line must not be swallowed while searching for a known keyword.
    assert(run("language ESSENCE' 1.0\nfind x : int(1..2)\nsuch that x = 1").ok());
    assert(!run("language ESSENCE' 1.0\nnot_a_statement\nfind x : int(1..2)").ok());

    // ---- Obligation 1: a sparse domain is a set. ---------------------------
    {
        const Translation t = runFile("languages/essence/instances/ok/sparse.eprime");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The bounds are there...
        assert(has(smt, "(>= x 1)"));
        assert(has(smt, "(<= x 5)"));
        // ...and so is the membership constraint, without which 2 and 4 are
        // admitted. Written as a disjunction of the three values.
        assert(has(smt, "(= 1 x)") || has(smt, "(= x 1)"));
        assert(has(smt, "(= 3 x)") || has(smt, "(= x 3)"));
        assert(has(smt, "(= 5 x)") || has(smt, "(= x 5)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A CONTIGUOUS domain gets no membership constraint, so the check above
        // is about sparseness rather than about domains in general. Without
        // this, a frontend that emitted a membership disjunction for every
        // domain would pass -- at the cost of a disjunction the size of the
        // range on every variable.
        const Translation t = run("language ESSENCE' 1.0\nfind y : int(0..10)\n"
                                  "such that y > 3\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(>= y 0)") && has(smt, "(<= y 10)"));
        assert(!has(smt, "(= 5 y)") && !has(smt, "(= y 5)"));
    }

    // ---- Obligation 3: the quantifier is expanded. -------------------------
    {
        const Translation t = runFile("languages/essence/instances/ok/queens.eprime",
                                      "languages/essence/instances/ok/queens.param");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // n = 4, so the matrix has four elements and each is bounded.
        assert(count(smt, "(select q 1)") >= 1);
        assert(count(smt, "(select q 4)") >= 1);
        // The shared pass emits one distinct over all four matrix cells.
        assert(SomtTest::hasDistinctArguments(t.parser(), {"(select q 1)", "(select q 2)", "(select q 3)", "(select q 4)"}));
        // The diagonal constraint is expanded to the six ordered pairs of
        // 1..4 with i < j -- not left as a quantifier, and not dropped.
        assert(count(smt, "abs") == 6);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));

        // The decision is on the record. Before allDiff became a Global this
        // frontend chose the encoding itself and the report said nothing, so a
        // reader could not tell "this language is insensitive to the profile"
        // from "this language never asked".
        bool recorded = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.unified_op == "alldifferent") { recorded = true; }
        }
        assert(recorded);
    }
    {
        // **The profile now changes the encoding**, which is the whole point of
        // routing allDiff through the pass. Essence' is the only frontend
        // besides MiniZinc that can reach the INDEXED shape, because it is the
        // only other one that declares a real HIR array rather than flattening
        // its matrix to scalars -- and the indexed shape is where ground and
        // quantified differ. The list shape is native distinct under both styles, by
        // design: a list has no index set to quantify over.
        //
        // `languages-scoping.md` §3.1 makes these four languages one cluster
        // BECAUSE they share the decomposition library. Until this landed, the
        // library was written once and used by one language, and
        // `--profile quantified` on an Essence' model was accepted and did
        // nothing.
        const Translation g = runFile("languages/essence/instances/ok/queens.eprime",
                                      "languages/essence/instances/ok/queens.param",
                                      "ground");
        const Translation q = runFile("languages/essence/instances/ok/queens.eprime",
                                      "languages/essence/instances/ok/queens.param",
                                      "quantified");
        assert(g.ok() && q.ok());
        const std::string gs = g.toSmt2();
        const std::string qs = q.toSmt2();
        // Not merely different text: the quantified one must contain a real
        // binder over the index set, and the ground one must not have left the
        // allDiff as a quantifier.
        assert(has(qs, "forall"));
        assert(!has(gs, "forall"));
        assert(SomtTest::hasDistinctArguments(g.parser(),
            {"(select q 1)", "(select q 2)", "(select q 3)", "(select q 4)"}));
        // Both are exact -- the two encodings differ in size and in solver
        // behaviour, not in what they preserve.
        assert(g.report().fidelity().sound && g.report().fidelity().complete && g.report().fidelity().preserves_optimum && g.report().fidelity().bounds.empty() && g.report().fidelity().count_status == CountStatus::UNASSESSED);
        assert(q.report().fidelity().sound && q.report().fidelity().complete && q.report().fidelity().preserves_optimum && q.report().fidelity().bounds.empty() && q.report().fidelity().count_status == CountStatus::UNASSESSED);
        // And both are readable back, which the quantified one especially
        // needs: it is the shape this parser had least exposure to.
        ParserPtr rg = newParser();
        ParserPtr rq = newParser();
        assert(rg->parseStr(gs));
        assert(rq->parseStr(qs));
    }
    {
        // The expansion follows the PARAMETER, so a different .param file must
        // produce a different model. This is the mechanical half: without it, a
        // frontend that expanded against a hard-coded bound would pass above.
        const Translation a = runFile("languages/essence/instances/ok/queens.eprime",
                                      "languages/essence/instances/ok/queens.param");
        const Translation b = run(
            "language ESSENCE' 1.0\nletting n be 5\n"
            "letting RANGE be domain int(1..n)\n"
            "find q : matrix indexed by [int(1..n)] of RANGE\n"
            "such that\n"
            "    allDiff(q),\n"
            "    forall i, j : int(1..n) . i < j -> |q[i] - q[j]| != j - i\n");
        assert(a.ok() && b.ok());
        // 4 elements against 5, and 6 diagonal pairs against 10.
        assert(count(a.toSmt2(), "abs") == 6);
        assert(count(b.toSmt2(), "abs") == 10);
    }
    {
        // An empty range is legal: `forall` over nothing is true. Refusing it
        // would reject a legal model, and returning nothing would drop the
        // constraint.
        const Translation t = run("language ESSENCE' 1.0\nfind x : int(0..3)\n"
                                  "such that forall i : int(3..1) . x = i\n");
        assert(t.ok());
    }

    // ---- Obligation 2: a matrix index is checked or constrained. -----------
    {
        // An undefined integer read makes this comparison false (manual 3).
        const Translation t = run(
            "language ESSENCE' 1.0\nletting n be 3\n"
            "find q : matrix indexed by [int(1..n)] of int(1..n)\n"
            "such that q[0] = 1\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(assert false)"));
    }
    {
        // An index INSIDE the domain is fine, so the check above is not simply
        // refusing every access.
        const Translation t = run(
            "language ESSENCE' 1.0\nletting n be 3\n"
            "find q : matrix indexed by [int(1..n)] of int(1..n)\n"
            "such that q[2] = 1\n");
        assert(t.ok());
        // ...and it emits no `(assert true)`: a constant index needs no
        // constraint, and one per access would be noise the size of the model.
        assert(!has(t.toSmt2(), "(assert true)"));
    }

    // ---- Obligation 4: `where` is about the parameters. --------------------
    {
        const Translation t = runFile("languages/essence/instances/reject/bad_where.eprime",
                                      "languages/essence/instances/reject/bad_where.param");
        assert(!t.ok());
        // E_TYPE, not an unsatisfiable model: the .param file is invalid for
        // this model, which is a different fact from "no solution exists".
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "not valid for this model"));
    }
    {
        // A `where` that HOLDS lets the model through, so the check is a check
        // rather than a refusal.
        const Translation t = run("language ESSENCE' 1.0\nletting n be 5\n"
                                  "where n > 2\nfind x : int(1..n)\nsuch that x = 1\n");
        assert(t.ok());
    }

    // ---- A parameter with no value is refused, not defaulted. --------------
    {
        const Translation t = runFile("languages/essence/instances/reject/no_param.eprime");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        // The message says what the parameter is FOR, so the refusal is not
        // mistaken for pedantry: a quantifier range is expanded against it.
        assert(has(t.diagnostics().all()[0].message, "quantifier range"));
    }
    {
        // A `given` domain is an input-validity condition. Treating n=5 as a
        // legal value of int(1..4) would elaborate a different source instance
        // while still producing a perfectly well-typed SMT formula.
        const Translation t = runFile(
            "languages/essence/instances/reject/bad_given.eprime",
            "languages/essence/instances/reject/bad_given.param");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "outside"));
        assert(has(t.diagnostics().all()[0].message, "not valid for the model"));
    }
    {
        // Parameter assignments are functions, not last-write-wins maps.
        const Translation t = runFile(
            "languages/essence/instances/reject/bad_given.eprime",
            "languages/essence/instances/reject/duplicate.param");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "more than once"));
    }
    {
        // Open parameter ranges are infinite but exact: n=4 belongs to
        // int(1..), and the finite domain derived from n remains materialised.
        const Translation t = runFile("languages/essence/instances/ok/queens.eprime",
                                      "languages/essence/instances/ok/queens.param");
        assert(t.ok());
    }

    // ---- Objectives. -------------------------------------------------------
    {
        const Translation t = runFile("languages/essence/instances/ok/opt.eprime");
        assert(t.ok());
        assert(has(t.toSmt2(), "OBJECTIVE_MIN"));
        assert(t.report().stats().num_objectives == 1);
    }
    {
        const Translation t = run("language ESSENCE' 1.0\nfind a : int(0..5)\n"
                                  "such that a >= 0\nmaximising a\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "OBJECTIVE_MAX"));
    }

    // ---- Essence' division rounds toward negative infinity. --------------
    {
        // With a positive divisor SMT-LIB div already rounds down, so the
        // floor correction folds away. Signed operands distinguish this
        // convention from truncation; exhaustive solver checks live in
        // test_essence_csplib_operators.py.
        const Translation t = run("language ESSENCE' 1.0\nfind a : int(-9..9)\n"
                                  "find b : int(-9..9)\nsuch that b = a div 2\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(div a 2)"));
        assert(t.semantics().stages()[0].source.assumptions.division
               == Sem::DivisionSemantics::FLOOR);
        assert(t.semantics().stages().size() == 2);
        assert(t.semantics().stages()[0].source.id == "essence-prime");
        assert(t.semantics().stages()[0].source.assumptions.undefined
               == Sem::UndefinedSemantics::RELATIONAL_FALSE);
    }
    {
        // The guard belongs inside the negation, at the numeric comparison.
        const Translation t = run(
            "language ESSENCE' 1.0\nfind x : int(-9..9)\n"
            "find d : int(-2..2)\nsuch that !(x div d = 1)\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(!has(smt, "(assert (distinct 0 d))"));
        bool recorded = false;
        for (const EncodingChoice& choice : t.report().choices()) {
            if (choice.strategy == "relational-definedness") { recorded = true; }
        }
        assert(recorded);
    }
    {
        // Matrix observables are projected under their source indices rather
        // than exposing the target SMT array as an implementation value.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find q : matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that q[1] = 3\n");
        assert(t.ok());
        Sem::Assignment target{{"(select q 1)", "3"}, {"(select q 2)", "8"}}, source;
        Diagnostics diags;
        assert(t.semantics().project(target, source, diags));
        assert(source.size() == 2);
        assert(source.at("q[1]") == "3");
        assert(source.at("q[2]") == "8");
    }

    // ---- Refusals and IO. --------------------------------------------------
    {
        // This asserted that the DECLARATION was refused as multi-dimensional
        // until 2026-09-20 (essence-prime.md §4.4). It pinned a limitation of
        // the subset rather than a property of Essence', so lifting the
        // limitation moved it -- and the input it used is still wrong, for a
        // different and more specific reason: `m[1]` reads a two-dimensional
        // matrix with one subscript. Kept, re-aimed at that, because a wrong
        // subscript ARITY is not an out-of-range index and reporting it as one
        // would send the reader to look at the bounds.
        const Translation t = run("language ESSENCE' 1.0\nletting n be 2\n"
                                  "find m : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n"
                                  "such that m[1] = 1\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "subscript"));
    }
    {
        // ...and the same declaration read correctly translates. The feature
        // is covered in test_essence_matrices.cpp; this row is here so the
        // one above cannot pass by the declaration still being refused.
        const Translation t = run("language ESSENCE' 1.0\nletting n be 2\n"
                                  "find m : matrix indexed by [int(1..n), int(1..n)] of int(1..n)\n"
                                  "such that m[1,1] = 1\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(select m 0)"));
    }
    {
        // A model with no `find` has no decision variables. It used to be
        // refused with E_PARSE; it now translates with a WARNING.
        //
        // The refusal's argument was that a vacuous model emits a trivially
        // satisfiable script whose `sat` reads as a success. That is a real
        // risk and it is why the warning says so in as many words. But it is
        // a true `sat` -- an empty vocabulary has exactly one model, the way
        // `p cnf 0 0` does -- and `languages/dimacs` accepts that shape
        // silently, so refusing here made two frontends disagree about the
        // same thing. Conjure accepts it too; `basic_enum_onlyDefn.eprime` in
        // the upstream corpus is its own test that it should.
        const Translation t = run("language ESSENCE' 1.0\nletting n be 3\n");
        assert(t.ok());
        bool warned = false;
        for (const Uir::Diagnostic& d : t.diagnostics().all()) {
            if (d.severity == Uir::Severity::WARNING
                && has(d.message, "no decision variables")) { warned = true; }
        }
        assert(warned);
        // ...and the warning does not become an error: the translation stands.
        assert(has(t.toSmt2(), "check-sat"));
    }
    {
        const Translation t = runFile("languages/essence/instances/nosuch.eprime");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- Coverage is honest. -----------------------------------------------
    {
        const Lang::OpCoverage& cov = e->coverage();
        assert(cov.supported < cov.total);
        assert(cov.missing.size() == cov.total - cov.supported);
    }

    // ---- Comprehension folds, which is how Conjure writes a quantifier. -----
    //
    // `and([ body | q : D ])` is `quantified()` with the generator written AFTER
    // the body, so the expansion is the same and the only new work is finding
    // the `|`: the body must be skipped before its generators can be read, then
    // re-parsed once per tuple. Twelve of the twenty-four upstream files stopped
    // here, reported as `'and' is not declared` -- a name the LANGUAGE provides,
    // blamed on the model for not declaring it.
    {
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find x : matrix indexed by [int(1..3)] of int(1..3)\n"
            "such that and([x[q] < 3 | q : int(1..3)])\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Expanded, not left as a quantifier: three instances, one per index.
        assert(count(smt, "(select x 1)") >= 1);
        assert(count(smt, "(select x 2)") >= 1);
        assert(count(smt, "(select x 3)") >= 1);
        assert(!has(smt, "forall"));
    }
    {
        // `or` folds with OR and `sum` with ADD. The three are one code path and
        // the kind selects the operator -- which is worth a test of its own,
        // because the kind was passed as a REFERENCE to the current token and
        // the first `eat()` overwrote it: every fold silently became a `sum`,
        // and a conjunction of Booleans came out as `+` over them.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find b : matrix indexed by [int(1..2)] of bool\n"
            "find n : int(0..9)\n"
            "such that or([b[q] | q : int(1..2)]),\n"
            "          n = sum([toInt(b[q]) | q : int(1..2)])\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The disjunction is a disjunction, not a sum.
        assert(has(smt, "(or "));
        // `toInt` is the Bool-to-Int coercion Essence' spells explicitly, and
        // `ite(b, 1, 0)` is the coercion rather than an encoding of it.
        assert(has(smt, "ite"));
    }
    {
        // A one-element list with NO generator is legal, and the fold is the
        // element: `and([e])`.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find p : bool\n"
            "such that and([p])\n");
        assert(t.ok());
    }
    {
        // Several generators are a cartesian product, as in `quantified`.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m : matrix indexed by [int(1..2)] of int(1..9)\n"
            "such that and([m[q] != m[r] \\/ q = r | q : int(1..2), r : int(1..2)])\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Two by two is four instances, and the two DIAGONAL ones have `q = r`
        // true, so the simplifier folds those disjuncts away. What must survive
        // is the two off-diagonal comparisons -- asserting a raw select count
        // would be asserting the simplifier's behaviour rather than the fold's.
        assert(has(smt, "(select m 1)"));
        assert(has(smt, "(select m 2)"));
        assert(count(smt, "(select m") >= 4);
    }

    std::cout << "All Essence' tests passed." << std::endl;
    return 0;
}
