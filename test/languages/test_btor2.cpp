// The BTOR2 frontend, and the obligations docs/languages/btor2.md wrote down
// before it existed.
//
// A BTOR2 file is a MACHINE, not a query, so the translation is an unrolling
// and every obligation is about what the unrolling must contain:
//
//   * a `state` with no `next` is a primary input under the BTOR2 specification,
//     hence fresh at every step. Adding a frame constraint removes legal traces
//     and can hide a real counterexample;
//   * a `state` with no `init` is UNCONSTRAINED at step 0. Defaulting it to
//     zero removes initial states, so a bad state reachable only from a
//     non-zero start becomes unreachable -- INCOMPLETE, reporting "safe" for a
//     circuit that is not.
//
// And the one that governs the whole translation: the unrolling is an
// UNDER-approximation. A trace found within k steps is real; "no trace within
// k" is not "safe". The fidelity entry must say so, and it is the only place
// that can.

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

Translation runFile(const std::string& path, int depth) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "btor2";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    return translate(u, opts);
}

Translation run(const std::string& src, int depth, const std::string& profile = "bmc") {
    Lang::SourceUnit u;
    u.main_path = "t.btor2";
    u.display_name = "t.btor2";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "btor2";
    opts.profile_id = profile;
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= BTOR2 frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* b = Lang::LanguageRegistry::instance().byId("btor2");
    assert(b != nullptr);

    // ---- The unrolling has the shape of the machine. -----------------------
    {
        const Translation t = runFile("languages/btor2/instances/ok/counter.btor2", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Three copies of the state -- steps 0, 1 and 2 -- not one.
        assert(has(smt, "counter@0") && has(smt, "counter@1") && has(smt, "counter@2"));
        // The init is at step 0 only.
        assert(has(smt, "(= #b00000000 counter@0)"));
        // The transition relates consecutive steps.
        assert(has(smt, "counter@1") && has(smt, "bvadd"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The depth is the depth. A machine unrolled to 2 and to 4 must give
        // different scripts, or the parameter is not doing anything.
        const Translation a = runFile("languages/btor2/instances/ok/counter.btor2", 2);
        const Translation c = runFile("languages/btor2/instances/ok/counter.btor2", 4);
        assert(a.ok() && c.ok());
        assert(a.toSmt2() != c.toSmt2());
        assert(count(c.toSmt2(), "counter@") > count(a.toSmt2(), "counter@"));
    }

    // ---- Obligation: a state with no `next` is nondeterministic. ------------
    {
        const Translation t = runFile("languages/btor2/instances/ok/frame.btor2", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The initial value is constrained, but later values are fresh. The bad
        // state can therefore be reached at step 1 exactly as the source allows.
        assert(has(smt, "(= #b0 held@0)") || has(smt, "(= held@0 #b0)"));
        assert(!has(smt, "(= held@0 held@1)") && !has(smt, "(= held@1 held@0)"));
        assert(!has(smt, "(= held@1 held@2)") && !has(smt, "(= held@2 held@1)"));
        assert(has(smt, "held@1") && has(smt, "held@2"));
    }
    {
        // A machine WITH a `next` gets only its declared transition equation.
        const Translation t = runFile("languages/btor2/instances/ok/counter.btor2", 1);
        const std::string smt = t.toSmt2();
        assert(!has(smt, "(= counter@0 counter@1)"));
    }

    // ---- Obligation: a state with no `init` is unconstrained at step 0. ----
    {
        const Translation t = runFile("languages/btor2/instances/ok/uninit.btor2", 1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // s is declared and NOT equated with zero at step 0. Defaulting it
        // would remove initial states and report "safe" for an unsafe circuit.
        assert(has(smt, "declare-fun s@0"));
        assert(!has(smt, "(= #b0 s@0)") && !has(smt, "(= s@0 #b0)"));
    }

    // ---- Obligation: constraints hold through the witness step. ------------
    {
        const Translation t = runFile("languages/btor2/instances/ok/constrained.btor2", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // All three candidate prefixes mention their respective input frame.
        assert(has(smt, "i@0") && has(smt, "i@1") && has(smt, "i@2"));
    }
    {
        // Step 0 satisfies both constraint and bad. The deterministic next
        // state violates the constraint at step 1, but a valid finite witness
        // ends at step 0 and must not be erased by the longer unrolling.
        const Translation t = run("1 sort bitvec 1\n2 zero 1\n3 one 1\n"
                                  "4 state 1 s\n5 init 1 4 2\n"
                                  "6 next 1 4 3\n7 not 1 4\n"
                                  "8 constraint 7\n9 bad 7\n", 1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(!has(smt, "(assert (= #b1 (bvnot s@1)))"));
    }

    // ---- The property asks about ANY step in 0..k. -------------------------
    {
        // A disjunction, so one satisfying assignment is a trace to the bad
        // state. Asserting it only at step k would miss a bad state reached
        // earlier, and asserting a conjunction would ask for a machine that is
        // bad at every step.
        const Translation t = runFile("languages/btor2/instances/ok/counter.btor2", 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, "(or "));
    }

    // ---- Complete safety-operator families. -------------------------------
    {
        const Translation t = runFile("languages/btor2/instances/ok/operators.btor2", 0);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Every source-side constant check simplifies to true. A wrong rotate,
        // reduction, or overflow encoding makes the conjunction false instead.
        assert(has(smt, "(assert true)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        const Translation t = run("1 sort bitvec 1\n2 sort bitvec 4\n"
                                  "3 input 2 x\n4 input 2 amount\n"
                                  "5 rol 2 3 4\n6 uaddo 1 3 4\n"
                                  "7 redor 1 5\n8 and 1 6 7\n9 bad 8\n", 0);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "bvurem"));
        assert(has(smt, "bvshl") && has(smt, "bvlshr"));
        assert(has(smt, "bvult"));
    }
    {
        // Exhaust the complete 3-bit carrier for the operators whose lowering
        // is relational rather than a one-to-one SMT opcode.
        const auto signed3 = [](unsigned value) {
            return value >= 4 ? static_cast<int>(value) - 8
                              : static_cast<int>(value);
        };
        const auto checkOverflow = [&](const std::string& op, unsigned a,
                                       unsigned b, bool expected) {
            const std::string src =
                "1 sort bitvec 1\n2 sort bitvec 3\n3 constd 2 "
                + std::to_string(a) + "\n4 constd 2 " + std::to_string(b)
                + "\n5 " + op + " 1 3 4\n6 constd 1 "
                + std::to_string(expected ? 1 : 0)
                + "\n7 eq 1 5 6\n8 bad 7\n";
            const Translation t = run(src, 0);
            assert(t.ok());
            assert(has(t.toSmt2(), "(assert true)"));
        };
        const auto checkRotate = [&](const std::string& op, unsigned a,
                                     unsigned b, unsigned expected) {
            const std::string src =
                "1 sort bitvec 1\n2 sort bitvec 3\n3 constd 2 "
                + std::to_string(a) + "\n4 constd 2 " + std::to_string(b)
                + "\n5 " + op + " 2 3 4\n6 constd 2 "
                + std::to_string(expected) + "\n7 eq 1 5 6\n8 bad 7\n";
            const Translation t = run(src, 0);
            assert(t.ok());
            assert(has(t.toSmt2(), "(assert true)"));
        };
        for (unsigned a = 0; a < 8; ++a) {
            for (unsigned b2 = 0; b2 < 8; ++b2) {
                const int sa = signed3(a), sb = signed3(b2);
                checkOverflow("uaddo", a, b2, a + b2 > 7);
                checkOverflow("usubo", a, b2, a < b2);
                checkOverflow("umulo", a, b2, a * b2 > 7);
                checkOverflow("saddo", a, b2, sa + sb < -4 || sa + sb > 3);
                checkOverflow("ssubo", a, b2, sa - sb < -4 || sa - sb > 3);
                checkOverflow("smulo", a, b2, sa * sb < -4 || sa * sb > 3);
                checkOverflow("sdivo", a, b2, sa == -4 && sb == -1);

                const unsigned amount = b2 % 3;
                const unsigned left = amount == 0
                    ? a
                    : ((a << amount) | (a >> (3 - amount))) & 7U;
                const unsigned right = amount == 0
                    ? a
                    : ((a >> amount) | (a << (3 - amount))) & 7U;
                checkRotate("rol", a, b2, left);
                checkRotate("ror", a, b2, right);
            }
        }
    }
    {
        // BTOR2 permits a bit-vector constant as an array initializer; it means
        // a constant array, not an ill-sorted array=bitvector equation.
        const Translation t = runFile("languages/btor2/instances/ok/array_init.btor2", 0);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "as const"));
        assert(has(smt, "select"));
    }
    {
        // `output` is an observable, not a bad property. It receives a defined
        // per-frame target symbol and participates in beta projection.
        const Translation t = run("1 sort bitvec 1\n2 one 1\n"
                                  "3 output 2 visible\n4 bad 2\n", 0);
        assert(t.ok());
        assert(has(t.toSmt2(), "visible@0"));
        bool projected = false;
        for (const auto& observable :
             t.semantics().stages().front().projection.observables) {
            projected = projected || observable.source_name == "visible@0";
        }
        assert(projected);
    }

    // ---- The bound is on the record, in the right direction. --------------
    {
        const Translation t = runFile("languages/btor2/instances/ok/counter.btor2", 3);
        assert(t.ok());
        const EncodingChoice* c = nullptr;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "transition-system") { c = &e; }
        }
        assert(c != nullptr);
        // sound and NOT complete: a trace found is real, "none found within k"
        // is not "safe". Backwards, this would claim the opposite.
        assert(c->fidelity.sound);
        assert(!c->fidelity.complete);
        assert(c->fidelity.bounds.size() == 1);
        assert(c->fidelity.bounds[0].kind == Fidelity::Bound::BMC_DEPTH);
        assert(c->fidelity.bounds[0].value == 3);
        // The rationale says what UNSAT does NOT mean, because that is the
        // reading a reader will otherwise supply.
        assert(has(c->rationale, "must not be reported as safe"));
        // The aggregate carries it too, so a report consumer sees the
        // approximation without walking the choices.
        assert(!t.report().fidelity().complete);
    }

    // ---- The depth has no default. -----------------------------------------
    {
        Lang::SourceUnit u;
        u.main_path = "languages/btor2/instances/ok/counter.btor2";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "btor2";
        opts.profile_id = "bmc";
        // No bmc_depth.
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        // The message says WHY there is no default, so it is not mistaken for
        // an oversight: the depth is the bound the fidelity is stated against.
        assert(has(t.diagnostics().all()[0].message, "no default"));
    }

    // ---- The default profile refuses it, and that is the floor working. ----
    {
        // Every built-in profile but `bmc` demands soundness AND completeness,
        // and a bounded unrolling cannot be complete. So a BTOR2 instance is
        // refused under `default` rather than translated with its
        // approximation unrecorded -- which is the floor doing its job, and the
        // reason `bmc` exists.
        const Translation t = run("1 sort bitvec 1\n2 constd 1 0\n3 state 1 s\n"
                                  "4 init 1 3 2\n5 next 1 3 3\n6 bad 3\n", 1, "default");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_FIDELITY_REJECTED);
    }

    // ---- Refusals. ----------------------------------------------------------
    {
        // The official grammar requires an init value to precede its state.
        const Translation t = run("1 sort bitvec 1\n2 state 1 s\n3 zero 1\n"
                                  "4 init 1 2 3\n5 bad 2\n", 0);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "state id must be greater"));
    }
    {
        // Initialization expressions cannot depend on time-varying inputs.
        const Translation t = run("1 sort bitvec 1\n2 input 1 i\n3 state 1 s\n"
                                  "4 init 1 3 2\n5 bad 3\n", 0);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "inputs are not allowed"));
    }
    {
        // Declared result sorts are checked even when the malformed node is not
        // reachable from the property.
        const Translation t = run("1 sort bitvec 1\n2 sort bitvec 4\n3 one 2\n"
                                  "4 add 1 3 3\n5 one 1\n6 bad 5\n", 0);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "declares result sort"));
    }
    {
        const Translation t = runFile("languages/btor2/instances/reject/liveness.btor2", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        // Liveness is a DIFFERENT problem, not a harder one: it asks about
        // infinite behaviour, and translating it as a safety property would
        // answer a different question with the right shape.
        assert(has(t.diagnostics().all()[0].message, "infinite behaviour"));
    }
    {
        const Translation t = runFile("languages/btor2/instances/reject/no_bad.btor2", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        // An unrolling with no property asserted is trivially satisfiable, so
        // translating it would report a "counterexample" for every circuit.
        assert(has(t.diagnostics().all()[0].message, "trivially satisfiable"));
    }
    {
        const Translation t = runFile("languages/btor2/instances/nosuch.btor2", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- Coverage is honest. -----------------------------------------------
    {
        const Lang::OpCoverage& cov = b->coverage();
        assert(cov.supported < cov.total);
        assert(cov.missing.size() == cov.total - cov.supported);
    }

    std::cout << "All BTOR2 tests passed." << std::endl;
    return 0;
}
