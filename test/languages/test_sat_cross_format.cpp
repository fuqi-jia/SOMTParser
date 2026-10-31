// DIMACS, QDIMACS and QCIR share Boolean expressions but retain distinct
// binding contracts. QDIMACS implicitly closes unbound matrix variables at
// the outermost existential level; QCIR keeps non-gate variables free.
// Both accept these inputs. These tests pin the differing HIR structures.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation run(const char* language, const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = language;
    return translate(u, opts);
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
    std::cout << "======= QBF cross-format obligations =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- The paired fixtures. -----------------------------------------------
    //
    // Both fixtures use variables absent from their explicit prefixes.
    const Translation qcir =
        run("qcir", "languages/qcir/instances/ok/free_by_default.qcir");
    const Translation qdimacs =
        run("qdimacs", "languages/qdimacs/instances/ok/free_variable.qdimacs");

    // QCIR: accepted, and the loose variables become free declarations.
    assert(qcir.ok());
    assert(has(qcir.toSmt2(), "declare-fun a"));
    assert(has(qcir.toSmt2(), "declare-fun b"));
    assert(qcir.report().stats().num_vars == 2);

    // QDIMACS: closed source; lifted witnesses stay target-private, including x2.
    assert(qdimacs.ok());
    assert(!has(qdimacs.toSmt2(), "(exists "));
    assert(lifted(qdimacs, "x2"));
    assert(has(qdimacs.toSmt2(), "declare-fun"));
    privateOnly(qdimacs, 2);
    // Output declarations include private witnesses, so source vocabulary is
    // compared through the semantic contract rather than declaration counts.
    assert(qcir.semantics().stages().back().source_signature.symbols.size() == 2);

    // ---- Neither rule is universal, so the frontends must not share it. -----
    {
        // Explicitly closed QDIMACS also declares no free variables.
        const Translation t = run("qdimacs", "languages/qdimacs/instances/ok/standard.qdimacs");
        assert(t.ok());
        assert(!has(t.toSmt2(), "declare-fun"));
    }
    {
        // ...and a QCIR file with everything quantified declares nothing free,
        // so QCIR's leniency is a default and not an inability to bind.
        const Translation t = run("qcir", "languages/qcir/instances/ok/prenex.qcir");
        assert(t.ok());
        assert(!has(t.toSmt2(), "declare-fun"));
    }

    // ---- What the two formats agree on. -------------------------------------
    // Worth pinning too: the disagreement above is one rule, not a general
    // divergence, and a reader who over-corrects would be as wrong as one who
    // under-corrects.
    {
        // Both scope the prefix over the WHOLE body, outermost block first.
        const Translation c = run("qcir", "languages/qcir/instances/ok/prenex.qcir");
        const Translation d = run("qdimacs", "languages/qdimacs/instances/ok/standard.qdimacs");
        assert(c.ok() && d.ok());
        for (const Translation* t : {&c, &d}) {
            const std::string smt = t->toSmt2();
            assert(smt.find("(forall ") < smt.find("(exists "));
            // One constraint each: the prefix is outside the conjunction.
            assert(t->report().stats().num_constraints == 1);
        }
    }
    {
        // Both report alternation depth on the same scale, which is what makes
        // the two arms comparable at all. A QCIR instance and a QDIMACS
        // instance at the same depth sit at the same level of the polynomial
        // hierarchy, and the experiment stratifies by that number
        // (qdimacs.md §4.3).
        const Translation c = run("qcir", "languages/qcir/instances/ok/prenex.qcir");
        const Translation d = run("qdimacs", "languages/qdimacs/instances/ok/standard.qdimacs");
        assert(c.ok() && d.ok());
        assert(c.report().stats().max_quantifier_alternations == 1);
        assert(d.report().stats().max_quantifier_alternations == 1);
    }

    // ---- The structural difference the pair exists to measure. --------------
    //
    // qdimacs.md §4.2: a CNF matrix arrives as ONE n-ary AND, so the QDIMACS arm
    // holds structure fixed at "none". qcir.md §4.8: QCIR arrives already
    // structured. That is the whole reason both are in the batch, and it is
    // observable here -- the QCIR translation of a comparable formula nests,
    // the QDIMACS one is flat.
    {
        const Translation d =
            run("qdimacs", "languages/qdimacs/instances/ok/standard.qdimacs");
        const Translation c =
            run("qcir", "languages/qcir/instances/ok/non_prenex.qcir");
        assert(d.ok() && c.ok());
        // QCIR can put a quantifier inside the body; QDIMACS cannot express one
        // at all, because a prefix is all it has. This is the structural axis
        // the two arms differ on, and it is why neither replaces the other.
        assert(c.report().stats().max_quantifier_alternations >= 1);
        const std::string cs = c.toSmt2();
        // The exists sits inside the forall's body rather than beside it: there
        // is an unclosed `(or` between them.
        const std::size_t f = cs.find("(forall ");
        const std::size_t e = cs.find("(exists ");
        assert(f < e);
        assert(has(cs.substr(f, e - f), "or"));
    }

    // ---- The second disagreement: what counts as the file's VOCABULARY. ----
    //
    // Three formats, three answers, and again each frontend looks right alone:
    //
    //     DIMACS    the HEADER. `p cnf V C` declares 1..V whether or not a
    //               clause mentions them -- an unmentioned variable is
    //               unconstrained, not absent.
    //     QDIMACS   the explicit PREFIX plus implicitly existential matrix
    //               variables. Unused explicit binders are retained.
    //     QCIR      the GATES. A variable nothing quantifies is free by default.
    //
    // The two "unused variable" fixtures are the same *shape* -- a declared or
    // quantified variable that no clause mentions -- and both must survive into
    // the translation. That much they agree on. What they disagree on is the
    // representation of their unquantified variables, asserted above.
    {
        const Translation d =
            run("dimacs", "languages/dimacs/instances/ok/unused_variable.cnf");
        assert(d.ok());
        // The header says three; only two are used; three are declared.
        assert(d.report().stats().num_vars == 3);
        assert(has(d.toSmt2(), "declare-fun x3"));

        const Translation q =
            run("qdimacs", "languages/qdimacs/instances/ok/unused_prefix_var.qdimacs");
        assert(q.ok());
        // The prefix binds three; only one is used; none is DECLARED, because
        // they are bound rather than free -- which is the same obligation
        // reaching a different representation, and the reason num_vars alone
        // cannot be compared across the two formats.
        assert(q.report().stats().num_vars == 0);
        assert(!has(q.toSmt2(), "declare-fun"));
        assert(has(q.toSmt2(), "x3"));
    }
    {
        // Both frontends retain out-of-header variables in tolerant mode.
        // DIMACS declares them free; QDIMACS existentially binds them.
        Lang::SourceUnit u;
        u.main_path = "t.cnf";
        u.display_name = "t.cnf";
        u.inline_source = "p cnf 1 1\n1 -5 0\n";
        TranslateOptions dopts;
        dopts.language_id = "dimacs";
        const Translation d = translate(u, dopts);
        assert(d.ok());
        assert(has(d.toSmt2(), "declare-fun x5"));

        TranslateOptions qopts;
        qopts.language_id = "qdimacs";
        const Translation q = translate(u, qopts);
        assert(q.ok());
        assert(lifted(q, "x5"));
        assert(!has(q.toSmt2(), "(exists "));
        privateOnly(q, 2);
    }
    {
        // And the negative control the whole battery rests on: DIMACS has no
        // quantifiers, so its alternation depth is zero. If this ever reported
        // otherwise, the statistic the QBF arms are stratified by would be
        // counting something else.
        const Translation d = run("dimacs", "languages/dimacs/instances/ok/simple.cnf");
        assert(d.ok());
        assert(d.report().stats().max_quantifier_alternations == 0);
    }

    std::cout << "All SAT/QBF cross-format tests passed." << std::endl;
    return 0;
}
