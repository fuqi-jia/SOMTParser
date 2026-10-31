// The SMT-LIB 2 baseline.
//
// This is the arm every other language is measured against: the same question,
// asked directly, so a difference in solver time between it and a translated
// benchmark is a property of the translation rather than of the question.
//
// It carries no reader -- the engine already parses SMT-LIB -- so almost
// nothing here is about parsing. What it is about is the BOUNDARY.
//
// The HIR covers less than the engine's node kinds. A baseline that silently
// translated the part it understood and dropped the rest would produce, under
// the name "SMT-LIB", a benchmark for a fragment nobody competes in, and would
// compare that against languages translated in full. docs/languages/smtlib2.md
// §4.1 calls this a second-filter failure of an unusual kind: the question is
// preserved perfectly and the CORPUS is silently replaced.
//
// So the assertions below come in two halves, and neither is meaningful alone:
// what the baseline carries must actually translate, and what it does not carry
// must be REFUSED BY NAME rather than dropped. A test that only did the first
// would pass against a frontend that translated one assertion and ignored the
// rest.

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

Translation run(const std::string& src, const std::string& name = "t.smt2") {
    Lang::SourceUnit u;
    u.main_path = name;
    u.display_name = name;
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "smtlib2";
    return translate(u, opts);
}

/** Translate, then read the result back with the engine. Both halves matter: a
 *  script that cannot be re-read is the defect class this project keeps
 *  finding. */
void trips(const std::string& src) {
    const Translation t = run(src);
    if (!t.ok()) {
        std::cout << "  FAILED to translate:\n" << src;
        if (!t.diagnostics().all().empty()) {
            std::cout << "  reason: " << t.diagnostics().all()[0].message << "\n";
        }
        assert(false);
    }
    ParserPtr reader = newParser();
    assert(reader->parseStr(t.toSmt2()));
}

/** Must refuse, and the message must name the construct -- so a coverage gap
 *  reads as a coverage gap rather than as a smaller model that succeeded. */
void refuses(const std::string& src, const std::string& named) {
    const Translation t = run(src);
    if (t.ok()) {
        std::cout << "  EXPECTED A REFUSAL for:\n" << src;
        assert(false);
    }
    assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT
           || t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    bool named_ok = false;
    for (const auto& d : t.diagnostics().all()) {
        if (has(d.message, named)) { named_ok = true; }
    }
    if (!named_ok) {
        std::cout << "  refusal did not name '" << named << "': "
                  << t.diagnostics().all()[0].message << "\n";
        assert(false);
    }
}

} // namespace

int main() {
    std::cout << "======= SMT-LIB 2 baseline =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* smt = Lang::LanguageRegistry::instance().byId("smtlib2");
    assert(smt != nullptr);

    // ---- Detection: .smt2 is shared with CHC, so sniff() decides. ----------
    {
        Lang::Language* chc = Lang::LanguageRegistry::instance().byId("chc");
        assert(chc != nullptr);
        const std::string horn = "(set-logic HORN)\n(declare-fun P (Int) Bool)";
        const std::string plain = "(set-logic QF_LIA)\n(declare-fun x () Int)";
        // A CHC file must not land here, and an ordinary one must not land in
        // CHC. Asserted as an ordering rather than as two thresholds, because
        // what matters is which wins the tie.
        assert(chc->sniff(horn) > smt->sniff(horn));
        assert(smt->sniff(plain) > chc->sniff(plain));
    }

    // ---- What the baseline carries. ----------------------------------------
    trips("(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n"
          "(assert (and (> x 0) (< (+ x y) 10)))\n(check-sat)\n");
    trips("(set-logic QF_BV)\n(declare-fun a () (_ BitVec 8))\n"
          "(assert (bvult a #x0f))\n(check-sat)\n");
    trips("(set-logic QF_ALIA)\n(declare-fun m () (Array Int Int))\n"
          "(assert (= (select (store m 1 2) 1) 2))\n(check-sat)\n");
    trips("(set-logic UF)\n(declare-sort U 0)\n(declare-fun f (U) U)\n"
          "(declare-fun c () U)\n(assert (= (f c) c))\n(check-sat)\n");
    trips("(set-logic LIA)\n(declare-fun P (Int) Bool)\n"
          "(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))\n(check-sat)\n");
    trips("(set-logic QF_S)\n(declare-fun s () String)\n"
          "(assert (> (str.len s) 3))\n(check-sat)\n");
    trips("(set-logic QF_LRA)\n(declare-fun r () Real)\n"
          "(assert (< (/ r 2.0) 1.5))\n(check-sat)\n");
    {
        // distinct, which had to be taught to yield Bool: mkOp's fallback gave
        // it widen(args), so `(distinct x y)` on two Ints recorded sort Int.
        trips("(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n"
              "(declare-fun z () Int)\n(assert (distinct x y z))\n(check-sat)\n");
    }

    // ---- A declared constant survives even if nothing mentions it. ---------
    {
        // §2.2: a `declare-fun` with zero arguments is part of the model's
        // vocabulary. Dropping an unused one changes what a model must assign,
        // and it is exactly the kind of thing a translation loses without
        // anything failing.
        const Translation t = run("(set-logic QF_LIA)\n(declare-fun x () Int)\n"
                                  "(declare-fun unused () Int)\n(assert (> x 0))\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(declare-fun unused () Int)"));
    }

    // ---- The logic the file asserts about itself is on the record. ---------
    {
        const Translation t = run("(set-logic QF_LIA)\n(declare-fun x () Int)\n"
                                  "(assert (> x 0))\n");
        assert(t.ok());
        const EncodingChoice* c = nullptr;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "set-logic") { c = &e; }
        }
        // A row that loses the logic cannot be grouped by division, which is
        // how SMT-COMP results are read.
        assert(c != nullptr);
        assert(c->strategy == "QF_LIA");
        assert(c->fidelity.sound && c->fidelity.complete && c->fidelity.preserves_optimum && c->fidelity.bounds.empty() && c->fidelity.count_status == CountStatus::UNASSESSED);
    }
    {
        // A different logic must produce a different record, so the field is
        // not a constant that happens to read right once.
        const Translation a = run("(set-logic QF_LIA)\n(declare-fun x () Int)\n"
                                  "(assert (> x 0))\n");
        const Translation b = run("(set-logic QF_LRA)\n(declare-fun x () Real)\n"
                                  "(assert (> x 0.0))\n");
        assert(a.ok() && b.ok());
        std::string la, lb;
        for (const EncodingChoice& e : a.report().choices()) {
            if (e.unified_op == "set-logic") { la = e.strategy; }
        }
        for (const EncodingChoice& e : b.report().choices()) {
            if (e.unified_op == "set-logic") { lb = e.strategy; }
        }
        assert(!la.empty() && la != lb);
    }

    // ---- What it does not carry is refused, by name. -----------------------
    {
        // A define-fun. This USED to be refused, on the argument that the HIR
        // has no body-carrying function and lifting it as an uninterpreted one
        // would turn a definition into an unconstrained symbol -- a strictly
        // weaker problem that translates cleanly and answers something else.
        //
        // The HIR now carries definition bodies. Retaining the source macro
        // also avoids changing a quantifier-free problem into a quantified UF
        // problem. The function must remain defined, not unconstrained.
        const Translation t = run("(set-logic QF_LIA)\n"
                                  "(define-fun double ((n Int)) Int (* 2 n))\n"
                                  "(declare-fun x () Int)\n"
                                  "(assert (= (double x) 4))\n(check-sat)\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(smt.find("(define-fun double ") != std::string::npos);
        assert(smt.find("(declare-fun double ") == std::string::npos);
        assert(smt.find("forall") == std::string::npos);
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // A real algebraic number.
        refuses("(set-logic QF_NRA)\n(declare-fun x () Real)\n"
                "(assert (= (* x x) 2.0))\n(assert (> x (root-obj (+ (^ x 2) (- 2)) 2)))\n"
                "(check-sat)\n", "root-obj");
    }
    {
        // A datatype sort is LIFTED now, and this case used to assert the
        // refusal. The HIR carried the whole theory -- SortKind::DATATYPE,
        // DatatypeDecl, the constructor/selector/tester expression kinds -- and
        // the lowering emitted it; only the lift had nothing, so the refusal
        // was never about a missing feature.
        //
        // What is asserted instead is that the declaration and its members
        // survive: the constructors must not ALSO be emitted as declare-funs,
        // which is a redeclaration the emitted script would refuse itself over.
        Translation t = run("(set-logic ALL)\n"
                            "(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n"
                            "(declare-fun p () Pair)\n(assert (= (fst p) 1))\n"
                            "(check-sat)\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(smt.find("(declare-datatypes ((Pair 0))") != std::string::npos);
        assert(smt.find("(declare-fun mk") == std::string::npos);
        assert(smt.find("(declare-fun fst") == std::string::npos);
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // The refusal must be FATAL, not a warning that leaves a smaller model.
        // This is the assertion the whole file exists for: a baseline that
        // dropped the unliftable assertion here would return a model with one
        // constraint, translate it, and report success.
        //
        // The example is `root-obj`, and the choice is the point.
        //
        // This case has used a define-fun, then a datatype, then a constant
        // array, and each stopped being unliftable in turn -- three times
        // testing that a closed gap is closed. Its own comment predicted the
        // decay twice and the prediction did not prevent it, because the
        // examples were all constructs refused FOR NOW.
        //
        // `root-obj` is refused ON PRINCIPLE: it is a Z3 extension and not
        // SMT-LIB, and this project's rule is that a non-standard spelling
        // stays refused. Everything that closed did so precisely because it
        // WAS standard. That is a reason the example will outlive the next
        // round of work, rather than a hope that it will.
        const Translation t = run(
            "(set-logic QF_NRA)\n"
            "(declare-fun x () Real)\n(assert (> x 0.0))\n"
            "(assert (> x (root-obj (+ (^ x 2) (- 2)) 2)))\n");
        assert(!t.ok());
        assert(t.report().stats().num_constraints == 0);
    }

    // ---- Coverage is measured and consistent. ------------------------------
    {
        const Lang::OpCoverage& cov = smt->coverage();
        assert(cov.supported < cov.total);
        // The invariant that made two earlier coverage tables lie: `missing`
        // must account for every gap the numbers claim.
        assert(cov.missing.size() == cov.total - cov.supported);
        // `missing` names what the frontend actually cannot take, and this
        // pins the construct the fatality case above uses -- so the two move
        // together instead of one silently outliving the other.
        bool names_root_obj = false;
        for (const std::string& m : cov.missing) {
            if (has(m, "root-obj")) { names_root_obj = true; }
        }
        assert(names_root_obj);
        // ...and the other direction, which is the half that catches a table
        // going stale rather than going wrong: a gap that has CLOSED must stop
        // being listed. Both earlier coverage tables in this project lied by
        // over-claiming, not by under-claiming -- and "define-fun" and
        // "algebraic datatypes" are the two that have since been removed.
        for (const std::string& m : cov.missing) {
            assert(!has(m, "define-fun"));
            assert(!has(m, "algebraic datatypes"));
            assert(!has(m, "as const"));
            assert(!has(m, "str.indexof_re"));
        }
    }

    {
        // A construct this build does not read is a COVERAGE GAP, not a
        // malformed file, and the two feed different statistics. Valid cvc5
        // extensions such as `set.is_empty` used to be reported as `E_PARSE: not a
        // well-formed SMT-LIB script`, a false claim about a valid benchmark
        // that also put it in the bucket measuring file quality rather than
        // the one measuring this reader's reach.
        //
        // The engine knew: it printed `Unknown or unexpected symbol` to
        // stderr and threw. What it did not do was CARRY that, so the
        // frontend could not act on it. `Parser::lastParseError()` is what
        // closed the gap.
        const Translation extension = run(
            "(set-logic ALL)\n(declare-fun x () (Set Int))\n"
            "(assert (set.is_empty x))\n(check-sat)\n");
        assert(!extension.ok());
        assert(extension.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        bool named = false;
        for (const Uir::Diagnostic& d : extension.diagnostics().all()) {
            if (d.message.find("set.is_empty") != std::string::npos) { named = true; }
        }
        assert(named);   // invariant 9: a refusal names the construct

        // ...and a genuinely malformed script stays E_PARSE. Without this the
        // change could have relabelled every failure and still passed above.
        //
        // The input matters, and a breakage probe is what showed it. The first
        // version used `(assert (> 1` -- an unexpected end of input, which
        // leaves NO recorded parse error at all, so a bucketing rule that
        // ignored the error's kind entirely still produced E_PARSE for it and
        // the test passed. `(set-logic QF_LIA) )` throws with a recorded kind
        // of SYNTAX, so it separates "checks the kind" from "checks only that
        // something was recorded", which is the distinction under test.
        const Translation malformed = run("(set-logic QF_LIA)\n)\n");
        assert(!malformed.ok());
        assert(malformed.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    {
        // A known extension arity error must not be hidden by lack of support.
        for (const auto& term : {"(nullable.some)", "(nullable.some 1 2)"}) {
            const Translation invalid = run(std::string("(assert ") + term + ")");
            assert(!invalid.ok());
            assert(invalid.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
            assert(has(invalid.diagnostics().all()[0].message, "wrong number of arguments"));
            assert(has(invalid.diagnostics().all()[0].message, "nullable.some"));
        }
        const Translation unsupported = run("(assert (= (nullable.some 1) (nullable.some 1)))");
        assert(!unsupported.ok());
        assert(unsupported.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        const Translation declared = run("(declare-fun |nullable.some| () Bool)(assert |nullable.some|)");
        assert(declared.ok());
    }

    std::cout << "All SMT-LIB 2 baseline tests passed." << std::endl;
    return 0;
}
