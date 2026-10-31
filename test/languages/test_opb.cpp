// The OPB / WBO frontend, and the obligations docs/languages/opb-wbo.md wrote
// down before it existed.
//
// Three of them are things no line of any file says:
//
//   1. **Every variable is Boolean**, taking values in {0,1}. OPB uses `x`
//      arithmetically in linear sums and nothing declares the domain, so it has
//      to be materialised -- as bounds on an Int rather than as a Bool sort,
//      because a Bool cannot be multiplied by a coefficient.
//   2. **`~x` is `(1 - x)`**, not a separate variable. Treating it as one
//      doubles the variable count and loses the relationship.
//   3. **A soft constraint's cost is incurred exactly when it is violated**, so
//      the objective is the reification of its negation.
//
// The fourth is written down and easy to read as decoration: **WBO's `soft: T ;`
// is a hard admissibility bound.** The cost must be STRICTLY less than T, and
// the format document's Example 3 has minimum cost exactly 6 with `soft: 6;` --
// the correct answer there is UNSATISFIABLE, not "optimum 6". Dropping T ADMITS
// assignments the format rejects, so the direction of the loss is sound = false
// and complete = true, which is easy to get backwards.
//
// The pairing against WCNF's `top` -- the same word for a different thing --
// lives in test/languages/test_pb_cross_format.cpp.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/opb.h"
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

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0, at = 0;
    while ((at = hay.find(needle, at)) != std::string::npos) { ++n; at += needle.size(); }
    return n;
}

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.opb";
    u.display_name = "t.opb";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "opb";
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "opb";
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= OPB / WBO frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* o = Lang::LanguageRegistry::instance().byId("opb");
    assert(o != nullptr);
    assert(o->extensions().size() == 2);

    // ---- The format document's own example, coefficient and all. ------------
    // 12345678901234567890 is 1.23e19 and LLONG_MAX is 9.22e18, so this is the
    // instance that made Expr::int_value unable to be the authoritative value.
    // Every digit has to survive.
    {
        const Translation t = runFile("languages/opb/instances/ok/spec_example.opb");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "12345678901234567890"));
        assert(has(smt, "define-objective"));
        assert(has(smt, "OBJECTIVE_MIN"));
        // Round-tripped in the Z3 dialect and not the default one. That is a
        // documented property rather than a workaround: this parser has its own
        // different `define-objective` grammar and does not recognise
        // `optimize-sat` at all, so OmtDialect::Z3 is the one spelling it reads
        // back (src/frontend/base_parser.cpp:3859).
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
    }

    // ---- Obligation 1: every variable is Boolean, and nothing says so. ------
    // Materialised as [0,1] bounds on an Int. A Bool sort would be wrong: these
    // variables are multiplied by coefficients and summed.
    {
        const Translation t = run("1 x1 +1 x2 >= 1 ;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun x1 () Int"));
        assert(!has(smt, "declare-fun x1 () Bool"));
        // Two bounds per variable, and they are what makes the domain real.
        assert(has(smt, "(>= x1 0)"));
        assert(has(smt, "(<= x1 1)"));
        assert(has(smt, "(>= x2 0)"));
        assert(has(smt, "(<= x2 1)"));
    }

    // ---- Obligation 2: `~x` is (1 - x). ------------------------------------
    {
        const Translation t = runFile("languages/opb/instances/ok/negated_literal.opb");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(- 1 x1)"));
        // Not a second variable: exactly two are declared.
        assert(t.report().stats().num_vars == 2);
        assert(!has(smt, "~"));
    }

    // ---- A product of literals is their arithmetic product. -----------------
    // Which is only correct BECAUSE of obligation 1: over {0,1} a product is a
    // conjunction, and without the bounds it would mean something else.
    {
        const Translation t = runFile("languages/opb/instances/ok/product.opb");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "*"));
        assert(t.report().stats().num_vars == 3);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- All six ASCII relational operators. --------------------------------
    // The restricted competition format permits only >= and =; a frontend
    // claiming the general format needs the rest, and `!=` is a disequality
    // rather than a comparison -- the one operator with no linear counterpart.
    {
        const Translation t = runFile("languages/opb/instances/ok/all_operators.opb");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, ">="));
        assert(has(smt, "<="));
        assert(has(smt, "distinct") || has(smt, "not"));
        assert(t.report().stats().num_constraints >= 6);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- WBO: the threshold, decided per instance. --------------------------
    {
        // T = 10, costs sum to 5: the threshold can never bind, so §4.4's
        // option B applies and it is exact() here. Native soft constraints
        // carry obligation 3 -- assert-soft means "cost incurred when
        // violated", which is the reification of the negation, without a
        // hand-built sum that would double-count.
        const Translation t = runFile("languages/opb/instances/ok/wbo_vacuous.wbo");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "assert-soft") == 2);
        assert(has(smt, ":weight 2"));
        assert(has(smt, ":weight 3"));
        // No relaxation machinery: the threshold is provably vacuous.
        assert(!has(smt, "!r0"));
        assert(!has(smt, "define-objective"));
    }
    {
        // T = 5 and the costs sum to 5, so an assignment violating both costs
        // exactly T -- which is NOT strictly less than T and therefore not a
        // solution. Option A is required: relaxation variables, the threshold
        // as a HARD constraint, and the cost sum as the objective.
        const Translation t = runFile("languages/opb/instances/ok/wbo_binding.wbo");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "!r0"));
        assert(has(smt, "!r1"));
        // Strictly less than T means <= T-1 = 4. Emitting `<= 5` would admit
        // exactly the assignments the format rejects, which is the whole point.
        assert(has(smt, " 4)"));
        assert(!has(smt, "(<= (+ (* !r0 2) (* !r1 3)) 5)"));
        assert(has(smt, "define-objective"));
        // Not soft: the costs are carried by the objective here, and emitting
        // both would count each violation twice.
        assert(!has(smt, "assert-soft"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
    }
    {
        // `soft: ;` is T = infinity: no threshold at all, so option B again.
        const Translation t = runFile("languages/opb/instances/ok/wbo_infinite.wbo");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "assert-soft"));
        assert(!has(smt, "!r0"));
    }
    {
        // The boundary: T exactly equal to sumcost BINDS, because the cost must
        // be strictly less than T. T = sumcost + 1 is the first vacuous value,
        // and this pair is where an off-by-one silently drops the threshold.
        const Translation binds = run("soft: 5 ;\n[2] 1 x1 >= 1 ;\n[3] 1 x2 >= 1 ;\n");
        const Translation vacuous = run("soft: 6 ;\n[2] 1 x1 >= 1 ;\n[3] 1 x2 >= 1 ;\n");
        assert(binds.ok() && vacuous.ok());
        assert(has(binds.toSmt2(), "!r0"));
        assert(!has(vacuous.toSmt2(), "!r0"));
    }
    {
        // Big costs: the vacuity check must be done in unbounded arithmetic,
        // because costs are big integers by design. Summed as long long these
        // two would overflow and the comparison would come out backwards.
        const Translation t = run(
            "soft: 100000000000000000000000 ;\n"
            "[99999999999999999999999] 1 x1 >= 1 ;\n");
        assert(t.ok());
        // sumcost = 99999999999999999999999 < T, so vacuous: soft, no relaxation.
        assert(has(t.toSmt2(), "assert-soft"));
        assert(!has(t.toSmt2(), "!r0"));
    }

    // ---- Malformed files. ---------------------------------------------------
    {
        // A soft constraint in a file with no `soft:` header is not a WBO file.
        const Translation t =
            runFile("languages/opb/instances/reject/soft_without_header.wbo");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "soft:"));
    }
    {
        // Costs are STRICTLY positive: zero is not "free to violate".
        const Translation t = runFile("languages/opb/instances/reject/zero_cost.wbo");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "positive"));
    }
    {
        const Translation t = runFile("languages/opb/instances/reject/no_semicolon.opb");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "';'"));
    }
    {
        // Every term needs a coefficient: a bare literal is not OPB.
        const Translation t = runFile("languages/opb/instances/reject/bare_literal.opb");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "coefficient"));
    }
    {
        const Translation t = runFile("languages/opb/instances/nosuch.opb");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- A statement may span lines, and a line may hold several. -----------
    // The format document warns explicitly against reading a line as a whole:
    // a constraint "may be very long", and `;` is the terminator.
    {
        const Translation split = run("1 x1\n+1 x2\n>= 1 ;\n");
        const Translation joined = run("1 x1 +1 x2 >= 1 ; 1 x3 >= 1 ;\n");
        assert(split.ok() && joined.ok());
        assert(split.report().stats().num_constraints == 1);
        assert(joined.report().stats().num_constraints == 2);
    }

    // Every cost indicator is now fixed by its source row. Counting remains
    // unassessed in metadata; the full source/cost relation is checked by the
    // independent Python oracle, rather than inferred from a format label.
    {
        const Translation t = runFile("languages/opb/instances/ok/wbo_binding.wbo");
        assert(t.ok());
        bool seen = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.strategy == "option-a-relaxation-vars") {
                seen = true;
                assert(c.fidelity.count_status == Uir::CountStatus::UNASSESSED);
                assert(c.fidelity.sound);       // and it costs nothing else
                assert(c.fidelity.complete);
            }
        }
        assert(seen);
    }

    std::cout << "All OPB/WBO tests passed." << std::endl;
    return 0;
}
