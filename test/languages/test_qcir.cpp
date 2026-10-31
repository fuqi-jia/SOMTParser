// The QCIR-G14 frontend, and the ten obligations docs/languages/qcir.md wrote
// down before it existed.
//
// That document's `implicit-constraints` block is a specification: each entry is
// something the format implies and does not write down, in the form
// "<what the format implies> => <what the frontend must emit>". Until now those
// entries were prose. This file is the first time they are executable, and every
// one of them is checked here or by a fixture in languages/qcir/instances.
//
// The one that matters most is §4.1, and it is worth stating plainly because it
// is invisible from either format alone:
//
//     QDIMACS 1.1: unquantified matrix variables are implicitly bound by an
//                  outermost existential quantifier.
//     QCIR-G14:    an unquantified non-gate variable IS FREE. Refusing it
//                  would reject a legal file.
//
// Both formats accept these inputs. Their tests preserve the distinct HIR
// structures: free declarations in QCIR and bound variables in QDIMACS.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/qcir.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <cassert>
#include <iostream>
#include <string>
#include <vector>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation run(const std::string& src, bool allowMissingHeader = false) {
    Lang::SourceUnit u;
    u.main_path = "t.qcir";
    u.display_name = "t.qcir";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "qcir";
    if (allowMissingHeader) { opts.parse.options["allow_missing_header"] = "true"; }
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "qcir";
    return translate(u, opts);
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0, at = 0;
    while ((at = hay.find(needle, at)) != std::string::npos) { ++n; at += needle.size(); }
    return n;
}

} // namespace

int main() {
    std::cout << "======= QCIR-G14 frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* q = Lang::LanguageRegistry::instance().byId("qcir");
    assert(q != nullptr);
    assert(q->extensions().size() == 1 && q->extensions()[0] == ".qcir");

    // Numeric input identifiers and their bound occurrences translate together.
    // The competition's headerless dialect is explicit opt-in.
    {
        const std::string body = "forall(1)\nexists(2)\noutput(3)\n3 = xor(1,2)\n";
        const auto numeric = run("#QCIR-G14\n" + body);
        VERIFY(numeric.ok());
        VERIFY(has(numeric.toSmt2(), "forall"));
        VERIFY(has(numeric.toSmt2(), "exists"));
        VERIFY(has(numeric.toSmt2(), "xor"));
        VERIFY(!has(numeric.toSmt2(), "declare-fun"));
        VERIFY(newParser()->parseStr(numeric.toSmt2()));
        VERIFY(!run(body).ok());
        const auto compatible = run(body, true);
        VERIFY(compatible.ok());
        VERIFY(compatible.toSmt2() == numeric.toSmt2());
        VERIFY(!compatible.diagnostics().all().empty());
        VERIFY(run("# Move variables:\n" + body, true).ok());
        VERIFY(!run("#QCIR-G15\n" + body, true).ok());
        VERIFY(!run("#QCIR-G140\n" + body, true).ok());
        VERIFY(!run("#QCIR-G14 3garbage\n" + body).ok());
        VERIFY(!run("#QCIR-G14 3 4\n" + body).ok());
    }

    // ---- The standard's own prenex example. ---------------------------------
    // forall v1. exists v2 v3. (v1 & v2) | (!v1 & !v2 & v3)
    {
        const Translation t = runFile("languages/qcir/instances/ok/prenex.qcir");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "forall"));
        assert(has(smt, "exists"));
        // The prefix scopes over the WHOLE body and in file order: forall
        // outside, exists inside. Reversing them changes the answer, and the
        // two spellings are both well-formed.
        assert(smt.find("forall") < smt.find("exists"));
        // No free variables: everything is quantified.
        assert(!has(smt, "declare-fun"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- The standard's non-prenex example. ---------------------------------
    // §2.2: a quantifier gate binds its variables only inside its subformula,
    // at whatever circuit position it occupies. x1 and x2 occur in g1 and are
    // bound by g2, one level up -- so a frontend cannot decide free-or-bound by
    // looking at the gate a name occurs in.
    {
        const Translation t = runFile("languages/qcir/instances/ok/non_prenex.qcir");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "forall"));
        assert(has(smt, "exists"));
        // The exists is INSIDE the forall's body, which is the whole point of
        // the format. If the frontend had hoisted it into a prefix, the two
        // would be adjacent at the top instead.
        assert(smt.find("forall") < smt.find("exists"));
        // x1 and x2 are bound, not free.
        assert(!has(smt, "declare-fun x1"));
        assert(!has(smt, "declare-fun x2"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- §4.1: an unquantified variable is FREE, not an error. --------------
    // The obligation with the highest risk in the whole document, because the
    // sibling format's rule is the opposite one and a reader who has just
    // written that frontend will reach for it.
    {
        const Translation t = runFile("languages/qcir/instances/ok/free_by_default.qcir");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun a"));
        assert(has(smt, "declare-fun b"));
        assert(t.report().stats().num_vars == 2);
    }
    {
        // ...and an explicit free block means the same thing.
        const Translation t = runFile("languages/qcir/instances/ok/free_block.qcir");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun a"));
        assert(has(smt, "declare-fun b"));
        assert(!has(smt, "declare-fun x"));      // x is quantified
        assert(has(smt, "exists"));
    }
    {
        // General QCIR permits the same source name free and quantified;
        // the restriction to one role belongs to cleansed form.
        const Translation t = run("#QCIR-G14\nfree(a)\nexists(a)\noutput(g1)\ng1 = and(a)\n");
        VERIFY(t.ok());
        VERIFY(newParser()->parseStr(t.toSmt2()));
        VERIFY(!run("#QCIR-G14 2\nfree(1)\nexists(1)\noutput(2)\n2 = and(1)\n").ok());
    }

    // ---- §4.2: empty gates are the truth constants. -------------------------
    // `and()` is true and `or()` is false. Both are legal -- the BNF's lit-list
    // derives epsilon -- and mkOp throws on an empty argument list rather than
    // inventing an identity, so this has to be a branch in the frontend and not
    // an accident of the builder.
    {
        const Translation t = runFile("languages/qcir/instances/ok/empty_gates.qcir");
        assert(t.ok());
        // or(true, false) is true, and the builders fold it. What is asserted is
        // that the file translated at all: an unhandled empty gate throws.
        const std::string smt = t.toSmt2();
        assert(has(smt, "assert"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Each polarity on its own, so a frontend that got one right and the
        // other backwards is caught. `and()` alone is true; `or()` alone is
        // false, and a false output makes the whole formula false.
        const Translation a = run("#QCIR-G14\noutput(g1)\ng1 = and()\n");
        assert(a.ok());
        assert(has(a.toSmt2(), "true"));
        const Translation o = run("#QCIR-G14\noutput(g1)\ng1 = or()\n");
        assert(o.ok());
        assert(has(o.toSmt2(), "false"));
    }

    // ---- §4.3: gates unreachable from the output are ignored. ---------------
    // Not an optimisation. Emitting them adds constraints the formula does not
    // have, and -- because a dead gate may mention variables nothing else does
    // -- changes the reported variable count for the same formula.
    {
        const Translation t = runFile("languages/qcir/instances/ok/dead_gate.qcir");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun a"));
        assert(!has(smt, "zzz"));
        assert(!has(smt, "qqq"));
        assert(t.report().stats().num_vars == 1);
    }

    // ---- §4.4: the two structural checks. -----------------------------------
    {
        // A cycle. The standard makes the circuit acyclic by requiring
        // definition before use -- for conforming files. A frontend meets
        // non-conforming ones, and an unchecked bottom-up walk does not
        // terminate on this input, so the check is what makes the walk correct.
        const Translation t = runFile("languages/qcir/instances/reject/cycle.qcir");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "itself"));
    }
    {
        const Translation t =
            runFile("languages/qcir/instances/reject/redefined_gate.qcir");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "more than once"));
    }
    {
        // Gate and input variables are disjoint namespaces.
        const Translation t =
            runFile("languages/qcir/instances/reject/quantified_gate.qcir");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "gate"));
    }
    {
        // General QCIR resolves repeated names to the innermost binder.
        const Translation t =
            run("#QCIR-G14\nexists(a)\nforall(a)\noutput(g1)\ng1 = and(a)\n");
        VERIFY(t.ok());
        VERIFY(newParser()->parseStr(t.toSmt2()));
        VERIFY(!run("#QCIR-G14 2\nexists(1)\nforall(1)\noutput(2)\n2 = and(1)\n").ok());
    }

    // ---- §4.5: the format identifier's count declares the dialect. ----------
    {
        // A cleansed file contains no xor and no ite gates at all. The header
        // says this one is cleansed and the body has an xor; believing the
        // header over the body would let a mislabelled file through silently.
        const Translation t =
            runFile("languages/qcir/instances/reject/cleansed_with_xor.qcir");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "cleansed"));
    }
    {
        // ...and the same gates in a general (uncounted) file are fine, so the
        // check is about the declared dialect and not about xor.
        const Translation t = runFile("languages/qcir/instances/ok/gates.qcir");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "xor"));
        assert(has(smt, "ite"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- §2.1: keywords are case-insensitive, variable names are not. -------
    // A frontend that lowercases the token stream once -- the obvious way to
    // handle AND versus and -- merges V1 and v1 into one variable and produces
    // a formula with fewer variables than the file has.
    {
        const Translation t = run("#QCIR-G14\nOUTPUT(g1)\ng1 = AND(V1, v1)\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun V1"));
        assert(has(smt, "declare-fun v1"));
        assert(t.report().stats().num_vars == 2);
    }

    // ---- §4.6: a quantified subcircuit, used twice. -------------------------
    //
    // Cleansed form forbids using a gate with a quantified subformula more than
    // once. The frontend does its part -- quantifier gates are rebuilt per use
    // rather than memoised, so every binder occurrence is built inside exactly
    // one scope. But qcir.md §4.6 predicted what happens next and it is worth
    // seeing rather than assuming: **the engine hash-conses**, so two
    // structurally identical `exists` terms become one node again, and
    // `(and E E)` folds to `E`. Sharing is not something this layer can opt out
    // of.
    //
    // So the assertion is semantic. The claim "not shared" is unobservable in
    // the emitted script and asserting it would be asserting a property of the
    // frontend that the layer below undoes -- which is §4.6's point: sharing of
    // quantified subterms is a MEASUREMENT the report should carry, not a
    // property the translation controls.
    {
        const Translation t = run(
            "#QCIR-G14\noutput(g3)\n"
            "g1 = and(x, y)\n"
            "g2 = exists(x; g1)\n"
            "g3 = and(g2, g2)\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "exists"));
        assert(has(smt, "declare-fun y"));      // y is free; x is bound
        assert(!has(smt, "declare-fun x"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Two DIFFERENT quantifier gates, so hash-consing cannot merge them.
        // This is what shows the frontend builds each independently: if
        // quantifier gates were memoised by gate index the way ordinary ones
        // are, the second would still be right here -- but a gate reused under
        // two different enclosing scopes would not be, and this is the shape
        // that catches it.
        const Translation t = run(
            "#QCIR-G14\noutput(g4)\n"
            "g1 = and(x, y)\n"
            "g2 = exists(x; g1)\n"
            "g3 = forall(x; g1)\n"
            "g4 = and(g2, g3)\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "exists"));
        assert(has(smt, "forall"));
        assert(has(smt, "declare-fun y"));
        assert(!has(smt, "declare-fun x"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // The same gate can contain a bound occurrence in one branch and a free
    // occurrence in another. Neither traversal order may contaminate its cache.
    for (const auto& inputs : {"g2, g1", "g1, g2"}) {
        const Translation t = run(
            std::string("#QCIR-G14\noutput(g3)\ng1 = and(x, y)\n")
            + "g2 = exists(x; g1)\ng3 = and(" + inputs + ")\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "declare-fun x"));
        VERIFY(has(t.toSmt2(), "declare-fun y"));
        VERIFY(newParser()->parseStr(t.toSmt2()));
    }
    {
        // Visiting the inner forall must restore the outer exists binding
        // before visiting its second operand x.
        const Translation t = run(
            "#QCIR-G14\noutput(g4)\ng1 = and(x, y)\n"
            "g2 = forall(x; g1)\ng3 = or(g2, x)\ng4 = exists(x; g3)\n");
        VERIFY(t.ok());
        VERIFY(!has(t.toSmt2(), "declare-fun x"));
        VERIFY(has(t.toSmt2(), "declare-fun y"));
        VERIFY(newParser()->parseStr(t.toSmt2()));
    }
    {
        const std::string nested =
            "output(4)\n2 = and(1)\n3 = exists(1; 2)\n4 = forall(1; 3)\n";
        VERIFY(run("#QCIR-G14\n" + nested).ok());
        VERIFY(!run("#QCIR-G14 4\n" + nested).ok());
        const std::string local =
            "free(1)\noutput(3)\n2 = and(1)\n3 = exists(1; 2)\n";
        VERIFY(run("#QCIR-G14\n" + local).ok());
        VERIFY(!run("#QCIR-G14 3\n" + local).ok());
    }

    // ---- Negation, which is a literal and not a gate. -----------------------
    {
        const Translation t = run("#QCIR-G14\noutput(-g1)\ng1 = and(a, -b)\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "not"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Files that are not QCIR at all. ------------------------------------
    {
        const Translation t = runFile("languages/qcir/instances/reject/not_qcir.qcir");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        const Translation t = runFile("languages/qcir/instances/reject/no_output.qcir");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "output"));
    }
    {
        // Two outputs: the circuit has one, by definition.
        const Translation t =
            run("#QCIR-G14\noutput(g1)\noutput(g1)\ng1 = and(a)\n");
        assert(!t.ok());
    }
    {
        // A missing file, and a directory, are IO errors and not parse errors --
        // the distinction the failure-cause table is built on.
        const Translation t = runFile("languages/qcir/instances/nosuch.qcir");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    std::cout << "All QCIR tests passed." << std::endl;
    return 0;
}
