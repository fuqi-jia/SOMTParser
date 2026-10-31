// The FlatZinc frontend, and the four obligations docs/languages/flatzinc.md
// wrote down before it existed.
//
// The fourth governs the whole design and is the reason this frontend refuses
// more than it accepts:
//
//     **An unrecognised builtin is E_UNSUPPORTED_CONSTRUCT, never a skipped
//     constraint.**
//
// FlatZinc's builtin catalogue IS the language, and it is *open* -- a solver may
// declare support for additional predicates -- so a frontend meets names it does
// not know as a matter of course. Skipping one drops a constraint: the model
// gets MORE solutions, and the answer looks like success.
//
// The first is the sharpest concrete one. `array_int_element(i, as, x)` becomes
// an ITE chain, and a chain's final `else` has to denote something -- so without
// `1 <= i <= |as|` it silently defines `as[i]` for an out-of-range `i`, which is
// a value the model never gave it and one a solver is free to choose.

#include "distinct_scope.h"
#include "somtparser/translation/translate.h"
#include "somtparser/languages/flatzinc.h"
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
    u.main_path = "t.fzn";
    u.display_name = "t.fzn";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "flatzinc";
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "flatzinc";
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= FlatZinc frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* f = Lang::LanguageRegistry::instance().byId("flatzinc");
    assert(f != nullptr);
    assert(f->extensions().size() == 1 && f->extensions()[0] == ".fzn");

    // ---- The governing obligation: refuse, never skip. ----------------------
    {
        const Translation t =
            runFile("languages/flatzinc/instances/reject/unknown_builtin.fzn");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        // The message names the builtin, so the coverage gap is actionable
        // rather than a bare "unsupported".
        assert(has(t.diagnostics().all()[0].message, "cumulative"));
        assert(has(t.diagnostics().all()[0].message, "weaken"));
    }

    // ---- Element carries its index bound. -----------------------------------
    {
        const Translation t = runFile("languages/flatzinc/instances/ok/element.fzn");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "ite"));
        // The bound is present and is over the ARRAY's length, which here is 3.
        // Without it the chain's `else` defines a[i] for i outside 1..3.
        assert(has(smt, "(<= 1 i)"));
        assert(has(smt, "(<= i 3)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The bound is on the ARRAY's length, not on the index variable's
        // declared domain -- those coincide in the fixture and must not be
        // conflated. Here the index is declared 1..9 and the array has two
        // entries, so the constraint has to say 2.
        const Translation t = run(
            "array [1..2] of int: a = [7, 8];\nvar 1..9: i;\nvar int: o;\n"
            "constraint array_int_element(i, a, o);\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(<= i 2)"));
    }

    // ---- bool2int gives its output the {0,1} domain. -----------------------
    {
        const Translation t = runFile("languages/flatzinc/instances/ok/bool2int.fzn");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "ite"));
        // On the VARIABLE, so the domain survives independently of this one
        // constraint.
        assert(has(smt, "(>= i 0)"));
        assert(has(smt, "(<= i 1)"));
    }

    // ---- Declared domains are materialised. --------------------------------
    // FlatZinc always writes the domain, so this is materialisation and not
    // inference -- but dropping it still widens the variable silently.
    {
        const Translation t = runFile("languages/flatzinc/instances/ok/domains.fzn");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(>= x 1)"));
        assert(has(smt, "(<= x 4)"));
        assert(has(smt, "(>= y 1)"));
        assert(has(smt, "(<= y 4)"));
        assert(t.report().stats().num_vars == 2);
    }

    // ---- Reification is generic. -------------------------------------------
    // The catalogue is open, so one case per `_reif` name would fall behind it.
    {
        const Translation t = runFile("languages/flatzinc/instances/ok/reified.fzn");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // b <-> (x = 3), written as an equality between two Bools. All four
        // spellings are accepted because `=` is commutative at BOTH levels and
        // the builders canonicalise child order -- pinning one would be
        // asserting the ordering rule rather than the reification.
        assert(has(smt, "(= (= x 3) b)") || has(smt, "(= b (= x 3))")
               || has(smt, "(= (= 3 x) b)") || has(smt, "(= b (= 3 x))"));
    }
    {
        // A reified LINEAR constraint, to show the handling is not special-cased
        // per family.
        const Translation t = run(
            "var 1..4: x;\nvar 1..4: y;\nvar bool: b;\n"
            "constraint int_lin_le_reif([1, 1], [x, y], 5, b);\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "b"));
    }
    {
        // `_imp(args,b)` is half reification: b implies the base relation.
        // Reversing it or treating it as equivalence changes the feasible set.
        const Translation t = run(
            "predicate int_le_imp(var int: a,var int: b,var bool: r);\n"
            "var 0..1: x;\nvar bool: b;\n"
            "constraint int_le_imp(5,x,b);\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(=> b (<= 5 x))"));
    }

    // ---- The builtin groups that are direct. -------------------------------
    {
        const Translation t = run(
            "var 1..9: a;\nvar 1..9: b;\nvar 1..9: c;\n"
            "constraint int_plus(a, b, c);\nconstraint int_times(a, b, c);\n"
            "constraint int_ne(a, b);\nconstraint int_abs(a, c);\n"
            "constraint int_max(a, b, c);\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "+"));
        assert(has(smt, "*"));
        assert(has(smt, "not") || has(smt, "distinct"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        const Translation t = runFile("languages/flatzinc/instances/ok/bool_clause.fzn");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "or"));
        assert(has(smt, "not"));
    }
    {
        // set_in over an explicit set literal is a disjunction of equalities.
        const Translation t = run(
            "var 1..9: x;\nconstraint set_in(x, [2, 4, 6]);\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "or"));
    }
    {
        // A decision set's finite carrier is an implicit declaration axiom,
        // while set_in remains the translated predicate relation.
        const Translation t = run(
            "var 1..2: x;\nvar set of {1,3,5}: s;\n"
            "constraint set_in_reif(x,s,false);\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "set.subset"));
        assert(has(smt, "set.member"));
        // One ordered interval axiom for x plus the finite carrier of s.
        assert(t.semantics().stages()[0].target_axioms.size() == 2);
    }
    {
        // Variable assignments are declaration axioms, not parameter aliases.
        // Dropping one leaves an output variable unconstrained.
        const Translation t = run(
            "var int: y;\nvar int: x :: output_var = y;\n"
            "constraint int_eq(y,3);\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(= x y)") || has(t.toSmt2(), "(= y x)"));
        assert(t.semantics().stages()[0].target_axioms.size() == 1);
    }
    {
        const Translation fixed_set = run(
            "var set of 1..3: s = {1,3};\nsolve satisfy;\n");
        assert(fixed_set.ok());
        assert(has(fixed_set.toSmt2(), "(= s (set.insert 1 3"));
        // The carrier and initializer are two separate A_Sigma obligations.
        assert(fixed_set.semantics().stages()[0].target_axioms.size() == 2);

        const Translation unbounded = run(
            "var set of int: s;\nsolve satisfy;\n");
        assert(!unbounded.ok());
        assert(unbounded.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(unbounded.diagnostics().all()[0].message, "finite upper carrier"));
    }
    {
        // FlatZinc arithmetic builtins are relations. A variable divisor must
        // be in the relation's domain; SMT-LIB's total div alone would admit a
        // result for d=0 that FlatZinc never defines.
        const Translation t = run(
            "var int: x;\nvar int: d;\nvar int: y;\n"
            "constraint int_div(x, d, y);\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(distinct 0 d)"));
        assert(t.semantics().stages().size() == 2);
        assert(t.semantics().stages()[0].source.id == "flatzinc");
        assert(t.semantics().stages()[0].source.assumptions.undefined
               == Sem::UndefinedSemantics::RELATIONAL_FALSE);
        bool recorded = false;
        for (const EncodingChoice& choice : t.report().choices()) {
            if (choice.strategy == "typed-relational-definedness") { recorded = true; }
        }
        assert(recorded);
    }

    // ---- all_different, and what it does NOT reach. ------------------------
    // Routed through ExprKind::GLOBAL's list shape and decomposed by the shared
    // pass. The ground/quantified profile axis still does not vary for a finite
    // list, because there is no source index set to quantify over.
    {
        const Translation t = run(
            "array [1..3] of var 1..3: q = [q1, q2, q3];\n"
            "var 1..3: q1;\nvar 1..3: q2;\nvar 1..3: q3;\n"
            "constraint all_different_int(q);\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(SomtTest::hasDistinctArguments(t.parser(), {"q1", "q2", "q3"}));
        assert(t.report().stats().num_vars == 3);
        // No quantifier: the quantified encoding is not reachable here.
        assert(t.report().stats().max_quantifier_alternations == 0);
    }

    // ---- Exact finite array/global relations used by real flatteners. ------
    {
        const Translation t =
            runFile("languages/flatzinc/instances/upstream/float_inf_range_dom.fzn");
        assert(t.ok());                         // array_bool_and
        assert(has(t.toSmt2(), "and"));
    }
    {
        // The initializer follows an annotation in canonical FlatZinc. It must
        // not be stripped together with `::var_is_introduced`.
        const Translation t =
            runFile("languages/flatzinc/instances/upstream/commutative_cse.fzn");
        assert(t.ok());                         // array_int_minimum
        const std::string smt = t.toSmt2();
        assert(has(smt, "x") && has(smt, "y") && has(smt, "z"));
    }
    {
        const Translation count =
            runFile("languages/flatzinc/instances/upstream/count_rewrite.fzn");
        const Translation lex =
            runFile("languages/flatzinc/instances/upstream/struct_lex.fzn");
        const Translation table =
            runFile("languages/flatzinc/instances/upstream/struct_table.fzn");
        const Translation element =
            runFile("languages/flatzinc/instances/upstream/test_bug_863.fzn");
        assert(count.ok() && lex.ok() && table.ok() && element.ok());
        assert(has(count.toSmt2(), "ite"));
        assert(has(lex.toSmt2(), "or"));
        assert(has(table.toSmt2(), "or"));
        assert(has(element.toSmt2(), "(<= 1 y)"));
        assert(has(element.toSmt2(), "(<= y 2)"));
    }

    // ---- The objective. -----------------------------------------------------
    {
        const Translation t = runFile("languages/flatzinc/instances/ok/objective.fzn");
        assert(t.ok());
        assert(t.report().stats().num_objectives == 1);
        assert(has(t.toSmt2(), "OBJECTIVE_MAX"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
    }

    // ---- Exactly one solve item. -------------------------------------------
    // The same rule minizinc.md §2.5 records, and the same two silent wrong
    // answers if it is not enforced.
    {
        const Translation t = runFile("languages/flatzinc/instances/reject/no_solve.fzn");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "solve"));
    }
    {
        const Translation t = runFile("languages/flatzinc/instances/reject/two_solve.fzn");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "more than one"));
    }

    // ---- Strategy annotations do not change constraints; output annotations
    //      define Obs/beta. --------------------------------------------------
    {
        const Translation plain = run("var 1..4: x;\nconstraint int_le(x, 3);\nsolve satisfy;\n");
        const Translation noisy = run(
            "var 1..4: x :: output_var :: var_is_introduced;\n"
            "constraint int_le(x, 3) :: defines_var(x);\n"
            "solve :: int_search([x], first_fail, indomain_min, complete) satisfy;\n");
        assert(plain.ok() && noisy.ok());
        assert(plain.toSmt2() == noisy.toSmt2());

        Sem::Assignment target{{"x", "2"}}, source;
        Diagnostics diags;
        assert(noisy.semantics().project(target, source, diags));
        assert(source.size() == 1 && source.at("x") == "2");
        assert(plain.semantics().project(target, source, diags));
        assert(source.empty());
    }
    {
        // output_array may contain fixed cells. Constants are reconstructed by
        // beta and do not require a synthetic target-model assignment.
        const Translation t = run(
            "array [1..3] of var int: a = [x, 2, y] :: output_array([1..3]);\n"
            "var int: x;\nvar int: y;\nsolve satisfy;\n");
        assert(t.ok());
        Sem::Assignment target{{"x", "7"}, {"y", "9"}}, source;
        Diagnostics diags;
        assert(t.semantics().project(target, source, diags));
        assert(source.at("a[1]") == "7");
        assert(source.at("a[2]") == "2");
        assert(source.at("a[3]") == "9");
    }

    {
        // Compiler-emitted set arrays retain fixed values and repeated aliases
        // without demanding fictitious assignments for literals or parameters.
        const Translation t = run(
            "set of int: p = {1,3}; set of int: q = p;\n"
            "var set of 1..3: s;\n"
            "array [1..7] of var set of int: a :: output_array([1..7]) "
            "= [{}, {1,3}, 1..2, p, q, s, s]; solve satisfy;\n");
        assert(t.ok());
        Sem::Assignment target{{"s", "{2}"}}, source;
        Diagnostics diags;
        assert(t.semantics().project(target, source, diags));
        assert(source.size() == 7);
        assert(source.at("a[1]") == "{}");
        assert(source.at("a[2]") == "{1,3}");
        assert(source.at("a[3]") == "1..2");
        assert(source.at("a[4]") == "{1,3}");
        assert(source.at("a[5]") == "{1,3}");
        assert(source.at("a[6]") == "{2}");
        assert(source.at("a[7]") == "{2}");
    }

    {
        const Translation t = runFile("languages/flatzinc/instances/nosuch.fzn");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    std::cout << "All FlatZinc tests passed." << std::endl;
    return 0;
}
