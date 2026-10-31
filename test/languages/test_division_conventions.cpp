// Which integer division each language means.
//
// The HIR carries three conventions and no default (test/hir/test_uir_division
// checks that they differ). This file checks the other half: that each frontend
// names the one ITS language specifies, rather than the one SMT-LIB has.
//
// The claim is made as a cross-path equality rather than by inspecting the
// emitted text, because inspecting the text would be checking the correction
// term instead of the choice. For each language:
//
//     the script the frontend produces  ==  the script DIV_TRUNC lowers to
//     the script the frontend produces  !=  the script DIV_EUCLID lowers to
//
// Neither line can be deleted on its own. Without the first, a frontend that
// emitted anything at all passes; without the second, a frontend that quietly
// used SMT-LIB's own div passes -- and that is the actual failure mode, because
// `div` is what the target language spells it and the two agree on every
// non-negative dividend.
//
// XCSP3 is checked against its official Java tools rather than by analogy with
// another CP format. TreeEvaluator and XNode evaluate DIV/MOD with Java long
// `/` and `%`, hence truncation toward zero and a remainder with the dividend's
// sign. The implementation revision used by this audit is recorded in
// docs/languages/xcsp3.md.

#include "somtparser/translation/translate.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace H = SOMTParser::Uir::Hir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation run(const std::string& src, const std::string& lang, const std::string& name) {
    Lang::SourceUnit u;
    u.main_path = name;
    u.display_name = name;
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = lang;
    return translate(u, opts);
}

/** The `(assert ...)` line of a script, which is where the operator shows. */
std::string assertLine(const std::string& s) {
    const std::size_t a = s.find("(assert");
    VERIFY(a != std::string::npos);
    return s.substr(a, s.find('\n', a) - a);
}

/** `y = op(x, k)` over declared Ints, lowered on its own. The reference the
 *  frontends are compared against. */
std::string reference(H::Op op, int k) {
    ParserPtr p = newParser();
    Lower::HirToParser lowered(p);
    Diagnostics d;
    TranslationReport report;

    H::ConstraintModel m;
    H::VarDecl x, y;
    x.name = "x"; x.sort = H::Sort::integer();
    y.name = "y"; y.sort = H::Sort::integer();
    m.decls.push_back(x);
    m.decls.push_back(y);
    H::Constraint c;
    c.formula = H::mkOp(H::Op::EQ,
                        {H::mkIdent("y", H::Sort::integer()),
                         H::mkOp(op, {H::mkIdent("x", H::Sort::integer()),
                                      H::mkInt(std::to_string(k))})});
    m.constraints.push_back(c);
    VERIFY(typeCheck(m, d));
    VERIFY(lowered.lower(m, report, d));
    VERIFY(!d.hasErrors());
    return assertLine(p->dumpSMT2());
}

} // namespace

int main() {
    std::cout << "======= division conventions, per language =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    const std::string trunc  = reference(H::Op::DIV_TRUNC, 2);
    const std::string euclid = reference(H::Op::DIV_EUCLID, 2);
    // The premise of every comparison below: the two references are not the
    // same script. If a later change collapsed the conventions, the per-language
    // assertions would all still "pass" against a single shared answer.
    VERIFY(trunc != euclid);

    // ---- MiniZinc: the Handbook says truncation. ---------------------------
    {
        const Translation t = run("var int: x;\nvar int: y;\n"
                                  "constraint y = x div 2;\nsolve satisfy;\n",
                                  "minizinc", "d.mzn");
        VERIFY(t.ok());
        const std::string line = assertLine(t.toSmt2());
        VERIFY(line == trunc);
        VERIFY(line != euclid);
    }
    {
        // mod follows div: MiniZinc's remainder takes the sign of the dividend,
        // so it is MOD_TRUNC and not SMT-LIB's never-negative mod.
        const Translation t = run("var int: x;\nvar int: y;\n"
                                  "constraint y = x mod 2;\nsolve satisfy;\n",
                                  "minizinc", "m.mzn");
        VERIFY(t.ok());
        const std::string line = assertLine(t.toSmt2());
        VERIFY(line == reference(H::Op::MOD_TRUNC, 2));
        VERIFY(line != reference(H::Op::MOD_EUCLID, 2));
    }
    {
        // `/` is Real division whatever its operands are. Source elaboration
        // makes every automatic Int-to-Float conversion explicit so the SMT
        // script does not depend on a target parser's coercion extension.
        const Translation real = run("var int: x;\nvar float: y;\n"
                                     "constraint y = x / 2;\nsolve satisfy;\n",
                                     "minizinc", "r.mzn");
        VERIFY(real.ok());
        VERIFY(has(real.toSmt2(), "(/ (to_real x) 2.0)"));

        // The operator itself works, and emits real division rather than one of
        // the integer conventions under another spelling.
        const Translation t = run("var int: x;\nvar int: y;\n"
                                  "constraint y = x / 2;\nsolve satisfy;\n",
                                  "minizinc", "r2.mzn");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(/ "));
        VERIFY(has(t.toSmt2(), "(to_real y)"));
        VERIFY(assertLine(t.toSmt2()) != trunc);
        VERIFY(assertLine(t.toSmt2()) != euclid);

        const Translation guarded = run(
            "var int: x;\nvar int: d;\nvar float: y;\n"
            "constraint y = x / d;\nsolve satisfy;\n",
            "minizinc", "r3.mzn");
        VERIFY(guarded.ok());
        VERIFY(has(guarded.toSmt2(), "distinct"));
        VERIFY(has(guarded.toSmt2(), "to_real d"));

        const Translation zero = run(
            "var float: y;\nconstraint y = 1.0 / 0.0;\nsolve satisfy;\n",
            "minizinc", "r4.mzn");
        VERIFY(zero.ok());
        VERIFY(has(zero.toSmt2(), "assert false"));

        Lang::Language* mzn = Lang::LanguageRegistry::instance().byId("minizinc");
        VERIFY(mzn != nullptr);
        const Lang::OpCoverage& cov = mzn->coverage();
        VERIFY(cov.missing.size() == cov.total - cov.supported);
        VERIFY(!cov.missing.empty());
        for (const std::string& missing : cov.missing) {
            VERIFY(!has(missing, "var float"));
        }
    }

    // ---- FlatZinc: inherits MiniZinc's, under an innocuous name. -----------
    {
        // `int_div(a, b, c)` is a predicate call meaning c = a div b. The name
        // gives no hint that a convention is being chosen, which is what makes
        // it worth a test of its own rather than trusting MiniZinc's.
        const Translation t = run("var int: x;\nvar int: y;\n"
                                  "constraint int_div(x, 2, y);\nsolve satisfy;\n",
                                  "flatzinc", "d.fzn");
        VERIFY(t.ok());
        const std::string line = assertLine(t.toSmt2());
        VERIFY(line == trunc);
        VERIFY(line != euclid);
    }
    {
        const Translation t = run("var int: x;\nvar int: y;\n"
                                  "constraint int_mod(x, 2, y);\nsolve satisfy;\n",
                                  "flatzinc", "m.fzn");
        VERIFY(t.ok());
        VERIFY(assertLine(t.toSmt2()) == reference(H::Op::MOD_TRUNC, 2));
    }

    // ---- The two languages agree, because one is the other's output. -------
    {
        // MiniZinc flattens TO FlatZinc, so a divergence between these two
        // would mean the pipeline disagrees with itself.
        const Translation mzn = run("var int: x;\nvar int: y;\n"
                                    "constraint y = x div 2;\nsolve satisfy;\n",
                                    "minizinc", "a.mzn");
        const Translation fzn = run("var int: x;\nvar int: y;\n"
                                    "constraint int_div(x, 2, y);\nsolve satisfy;\n",
                                    "flatzinc", "a.fzn");
        VERIFY(mzn.ok() && fzn.ok());
        VERIFY(assertLine(mzn.toSmt2()) == assertLine(fzn.toSmt2()));
    }

    // ---- XCSP3: official Java evaluation is truncation toward zero. --------
    {
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\">\n"
            "<variables><var id=\"x\"> 0..10 </var><var id=\"y\"> 0..10 </var></variables>\n"
            "<constraints><intension> eq(y,div(x,2)) </intension></constraints>\n"
            "</instance>\n", "xcsp3", "d.xml");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // XCSP3 variables always carry finite-domain assertions, so the
        // division relation is not the script's first `(assert ...)` line.
        VERIFY(has(smt, trunc));
        VERIFY(!has(smt, euclid));
        VERIFY(t.semantics().stages().size() == 2);
        VERIFY(t.semantics().stages()[0].source.id == "xcsp3");
        VERIFY(t.semantics().stages()[0].source.assumptions.division
               == Uir::Sem::DivisionSemantics::TRUNCATE_TOWARD_ZERO);
    }
    {
        // A variable divisor remains partial. XCSP3 intension is satisfied only
        // when its root predicate evaluates to 1, so the guard propagates to
        // that root even through Boolean negation.
        const Translation t = run(
            "<instance format=\"XCSP3\" type=\"CSP\">"
            "<variables><var id=\"x\"> -10..10 </var><var id=\"y\"> -2..2 </var>"
            "</variables><constraints><intension> not(eq(div(x,y),1)) </intension>"
            "</constraints></instance>", "xcsp3", "partial.xml");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(distinct 0 y)"));
        // The simplifier rewrites `not (= term 1)` to `distinct 1 term`.
        // The domain guard must remain the outer conjunction, not be negated.
        VERIFY(has(smt, "(assert (and (distinct 0 y) (distinct 1 "));
        bool recorded = false;
        for (const EncodingChoice& choice : t.report().choices()) {
            if (choice.strategy == "constraint-root-definedness") { recorded = true; }
        }
        VERIFY(recorded);
    }

    // ---- Division by zero uses the typed relational core. ------------------
    {
        // A literal non-zero divisor cannot divide by zero, so the translation
        // is exact and carries no entry. Without this, the frontend could mark
        // every division unsound and still pass the test below -- and under the
        // default profile's fidelity floor that would refuse to translate any
        // model containing a division at all.
        const Translation t = run("var int: x;\nvar int: y;\n"
                                  "constraint y = x div 2;\nsolve satisfy;\n",
                                  "minizinc", "z1.mzn");
        VERIFY(t.ok());
        VERIFY(t.report().fidelity().sound && t.report().fidelity().complete && t.report().fidelity().preserves_optimum && t.report().fidelity().bounds.empty() && t.report().fidelity().count_status == CountStatus::UNASSESSED);
        for (const EncodingChoice& c : t.report().choices()) {
            VERIFY(c.unified_op != "partial-expression");
        }
    }
    {
        // A variable divisor can be zero. The frontend must carry `(y != 0)`
        // with the value and close the equality as `(y != 0) and (...)`; a
        // global `y != 0` would be wrong under a false implication antecedent.
        const Translation t = run("var int: x;\nvar int: y;\nvar int: z;\n"
                                  "constraint z = x div y;\nsolve satisfy;\n",
                                  "minizinc", "z2.mzn");
        VERIFY(t.ok());
        bool found = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.unified_op == "partial-expression") {
                found = true;
                VERIFY(c.fidelity.sound && c.fidelity.complete && c.fidelity.preserves_optimum && c.fidelity.bounds.empty() && c.fidelity.count_status == CountStatus::UNASSESSED);
                VERIFY(c.strategy == "typed-relational-definedness");
            }
        }
        VERIFY(found);
        VERIFY(t.report().fidelity().sound && t.report().fidelity().complete && t.report().fidelity().preserves_optimum && t.report().fidelity().bounds.empty() && t.report().fidelity().count_status == CountStatus::UNASSESSED);
        VERIFY(has(t.toSmt2(), "(distinct 0 y)"));
        VERIFY(t.semantics().stages().size() == 2);
        VERIFY(t.semantics().stages()[0].source.id == "minizinc");
        VERIFY(t.semantics().stages()[0].target.id == "typed-relational-core");
        VERIFY(t.semantics().stages()[1].target.id == "smt-lib");
    }
    {
        // The motivating case: the guard belongs inside the consequent, so
        // x=0,b=false remains feasible and x=0,b=true does not.
        const Translation t = run("var 0..10: x;\nvar bool: b;\n"
                                  "constraint b -> 10 div x = 10;\n"
                                  "solve minimize x;\n",
                                  "minizinc", "guarded.mzn");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2(Lower::OmtDialect::Z3);
        VERIFY(has(smt, "(=> b (and (distinct 0 x)"));
        VERIFY(has(smt, "(minimize x)"));
        VERIFY(t.semantics().stages().size() == 2);
        VERIFY(t.semantics().stages()[1].target.id == "omt");
        VERIFY(t.semantics().fidelity().sound && t.semantics().fidelity().complete && t.semantics().fidelity().preserves_optimum && t.semantics().fidelity().bounds.empty() && t.semantics().fidelity().count_status == CountStatus::UNASSESSED);
        VERIFY(t.semantics().fidelity().sound == t.report().fidelity().sound);
        VERIFY(t.semantics().fidelity().complete == t.report().fidelity().complete);
        VERIFY(t.semantics().fidelity().preserves_optimum
               == t.report().fidelity().preserves_optimum);
        int semantic_stages = 0;
        for (const EncodingChoice& choice : t.report().choices()) {
            if (choice.unified_op == "semantic-translation-stage") {
                ++semantic_stages;
            }
        }
        VERIFY(semantic_stages == 2);
    }
    {
        // Definition failure becomes false at the nearest Boolean relation.
        // Consequently negating that relation is true, and using it as an
        // implication antecedent makes the implication true. A global x!=0 or
        // i-in-range assertion would incorrectly make this model UNSAT.
        const Translation t = run(
            "array[1..1] of var bool: a;\n"
            "var 2..2: i;\n"
            "var 0..0: x;\n"
            "constraint not a[i];\n"
            "constraint not (10 div x = 10);\n"
            "constraint (10 div x = 10) -> false;\n"
            "solve satisfy;\n",
            "minizinc", "partial_boolean_contexts.mzn");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(not (and (select a i) (and (<= i 1) (>= i 1))))"));
        VERIFY(has(smt, "(not (and (distinct 0 x)"));
        VERIFY(has(smt, "(=> (and (distinct 0 x)"));
        VERIFY(!has(smt, "(assert (distinct 0 x))"));
        VERIFY(!has(smt, "(assert (<= i 1))"));
        VERIFY(!has(smt, "(assert (>= i 1))"));
    }
    {
        // A lossy pass must downgrade both audit channels. Otherwise the
        // semantic theorem would say exact while the experiment report says
        // bounded under-approximation.
        Lang::SourceUnit unit;
        unit.inline_source = "var int: x;\nconstraint x = x;\nsolve satisfy;\n";
        unit.display_name = "bounded.mzn";
        TranslateOptions opts;
        opts.language_id = "minizinc";
        opts.profile_id = "bv32";
        const Translation t = translate(unit, opts);
        VERIFY(t.ok());
        VERIFY(!t.report().fidelity().complete);
        VERIFY(!t.semantics().fidelity().complete);
        VERIFY(t.report().fidelity().bounds.size()
               == t.semantics().fidelity().bounds.size());
    }

    std::cout << "All division-convention tests passed." << std::endl;
    return 0;
}
