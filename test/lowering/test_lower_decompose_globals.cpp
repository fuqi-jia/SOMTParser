// alldifferent, encoded two ways, end to end.
//
// This is the pass that makes EncodingProfile::style() mean something. Until it
// existed, `ground` and `quantified` were two names for identical output, and
// translate() said so out loud on every run (docs/hir-design-decisions-
// 2026-08-12.md §3.2). The property that matters is not "the pass runs" but
// "the two profiles produce different scripts, and both are right":
//
//   ground     AND over lo<=i<j<hi of  (not (= (select a i) (select a j)))
//   quantified forall i j. (lo<=i<hi and lo<=j<hi and i<j) -> ...
//
// Both are Fidelity::exact(), so no fidelity check can tell them apart and only
// the emitted text can. Hence the assertions below are on the text.
//
// The asymmetry in §4 is real rather than an implementation limit: ground has
// to *enumerate* the index range, so it needs constant bounds; quantified does
// not. A model with variable bounds therefore translates under one profile and
// not the other, and that is reported by name rather than guessed around.

#include "somtparser/lowering/bound_ints_pass.h"
#include "somtparser/lowering/decompose_globals_pass.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/hir/typecheck.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

namespace H = SOMTParser::Uir::Hir;

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0;
    for (std::size_t at = hay.find(needle); at != std::string::npos;
         at = hay.find(needle, at + needle.size())) {
        ++n;
    }
    return n;
}

/** A model with `a : (Array Int Int)` and alldifferent(a, 0, n). */
H::ConstraintModel modelWithAllDifferent(H::ExprPtr lo, H::ExprPtr hi) {
    H::ConstraintModel m;
    H::VarDecl a;
    a.name = "a";
    a.sort = H::Sort::array(H::Sort::integer(), H::Sort::integer());
    m.decls.push_back(a);

    H::Constraint c;
    c.formula = H::mkGlobal("alldifferent",
                            {H::mkIdent("a", a.sort), std::move(lo), std::move(hi)});
    m.constraints.push_back(c);
    return m;
}

/** Run the pass under one style and return the emitted SMT-LIB. */
bool encode(const char* profile_id, H::ConstraintModel model, std::string& out,
            Diagnostics& diags) {
    Lower::registerBuiltinPasses(PassRegistry::instance());
    const auto profile = EncodingProfile::builtin(profile_id);
    VERIFY(profile != nullptr);

    TranslationReport report;
    if (!PassManager::run(model, *profile, PassRegistry::instance(), report, diags)) {
        return false;
    }
    // The decomposed model must still type-check: a pass that produces an
    // ill-sorted model is worse than one that refuses, and nothing downstream
    // re-checks.
    VERIFY(H::typeCheck(model, diags));

    ParserPtr p = newParser();
    Lower::HirToParser lowered(p);
    if (!lowered.lower(model, report, diags)) { return false; }
    out = p->dumpSMT2();
    return true;
}

} // namespace

int main() {
    std::cout << "======= decompose-globals: alldifferent two ways =======\n";

    // ---- The pass declares what it does, which is what retires the warning. -
    {
        Lower::registerBuiltinPasses(PassRegistry::instance());
        const Pass* p = PassRegistry::instance().get("decompose-globals");
        VERIFY(p != nullptr);
        VERIFY(p->traits().reads_encoding_style);
        // It eliminates the feature a model with a global reports, so
        // PassManager::validate stops rejecting such a model once it is in the
        // pipeline.
        const auto t = p->traits();
        bool eliminates_globals = false;
        for (const auto& f : t.eliminates) {
            if (f == feat::globalConstraint()) { eliminates_globals = true; }
        }
        VERIFY(eliminates_globals);

        // Both style profiles run it, which is what makes them differ.
        for (const char* id : {"ground", "quantified"}) {
            const auto prof = EncodingProfile::builtin(id);
            VERIFY(prof != nullptr);
            VERIFY(encodingStyleIsConsumed(*prof, PassRegistry::instance()));
        }
    }

    // ---- A model with a global reports the feature. --------------------------
    // Without this, decompose-globals could eliminate a feature nothing
    // produces -- the vacuous-check shape test_uir_feature_reachability.cpp
    // exists to make visible.
    {
        const auto m = modelWithAllDifferent(H::mkInt(0), H::mkInt(4));
        const auto f = m.features();
        VERIFY(f.count(feat::globalConstraint()) == 1);
    }

    // ---- Ground: each selected element appears once. -----------------------
    {
        std::string smt;
        Diagnostics d;
        VERIFY(encode("ground", modelWithAllDifferent(H::mkInt(0), H::mkInt(4)), smt, d));
        VERIFY(!d.hasErrors());

        VERIFY(count(smt, "(select a ") == 4);
        VERIFY(count(smt, "(distinct ") == 1);
        VERIFY(!contains(smt, "forall"));
        VERIFY(!contains(smt, "alldifferent"));
    }

    // ---- Quantified: one assertion whatever the range. ----------------------
    {
        std::string smt;
        Diagnostics d;
        VERIFY(encode("quantified", modelWithAllDifferent(H::mkInt(0), H::mkInt(4)),
                      smt, d));
        VERIFY(!d.hasErrors());

        VERIFY(contains(smt, "forall"));
        // Two selects total, regardless of the range.
        VERIFY(count(smt, "(select a ") == 2);
        VERIFY(!contains(smt, "alldifferent"));
    }

    // ---- The two really are different scripts. ------------------------------
    // The assertion the whole feature exists for. If this ever passes by
    // accident -- both profiles emitting the same text -- everything above
    // could still be true while the axis measured nothing.
    {
        std::string g, q;
        Diagnostics dg, dq;
        VERIFY(encode("ground", modelWithAllDifferent(H::mkInt(0), H::mkInt(64)), g, dg));
        VERIFY(encode("quantified", modelWithAllDifferent(H::mkInt(0), H::mkInt(64)), q, dq));
        VERIFY(g != q);
        VERIFY(g.size() > q.size());   // ground is the larger encoding, at n=64
    }

    // ---- Size scales as the encodings promise. ------------------------------
    // Native distinct selects each element once; the quantified form is fixed.
    {
        std::string g4, g8, q4, q8;
        Diagnostics d;
        VERIFY(encode("ground", modelWithAllDifferent(H::mkInt(0), H::mkInt(4)), g4, d));
        VERIFY(encode("ground", modelWithAllDifferent(H::mkInt(0), H::mkInt(8)), g8, d));
        VERIFY(encode("quantified", modelWithAllDifferent(H::mkInt(0), H::mkInt(4)), q4, d));
        VERIFY(encode("quantified", modelWithAllDifferent(H::mkInt(0), H::mkInt(8)), q8, d));
        VERIFY(count(g8, "(select a ") == 8);
        VERIFY(count(g4, "(select a ") == 4);
        VERIFY(count(q8, "(select a ") == count(q4, "(select a "));
        VERIFY(g8.size() > g4.size());
        VERIFY(q8.size() == q4.size() || q8.size() - q4.size() < 8);  // only the bound differs
    }

    // ---- Degenerate ranges are vacuous, not malformed. ----------------------
    // Fewer than two elements means nothing to compare. mkOp(AND, {}) throws --
    // dimacs-cnf.md §4.1's trap -- so the encoding must produce `true`.
    {
        for (long long hi : {0LL, 1LL}) {
            std::string smt;
            Diagnostics d;
            VERIFY(encode("ground", modelWithAllDifferent(H::mkInt(0), H::mkInt(hi)),
                          smt, d));
            VERIFY(!d.hasErrors());
            VERIFY(count(smt, "(select a ") == 0);
        }
    }

    // ---- Ground needs constant bounds; quantified does not. -----------------
    // A real asymmetry, reported by name rather than guessed around.
    {
        H::VarDecl n;
        n.name = "n";
        n.sort = H::Sort::integer();

        auto withVariableBound = [&]() {
            H::ConstraintModel m = modelWithAllDifferent(H::mkInt(0),
                                                         H::mkIdent("n", n.sort));
            m.decls.push_back(n);
            return m;
        };

        std::string smt;
        Diagnostics dg;
        VERIFY(!encode("ground", withVariableBound(), smt, dg));
        VERIFY(dg.hasErrors());
        VERIFY(dg.firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);

        Diagnostics dq;
        VERIFY(encode("quantified", withVariableBound(), smt, dq));
        VERIFY(!dq.hasErrors());
        VERIFY(contains(smt, "forall"));
    }

    // ---- The choice is recorded, so a result row can say which was used. ----
    {
        for (const auto& tc : {std::make_pair("ground", "alldifferent-distinct"),
                               std::make_pair("quantified", "alldifferent-quantified")}) {
            Lower::registerBuiltinPasses(PassRegistry::instance());
            auto model = modelWithAllDifferent(H::mkInt(0), H::mkInt(3));
            const auto profile = EncodingProfile::builtin(tc.first);
            TranslationReport report;
            Diagnostics d;
            VERIFY(PassManager::run(model, *profile, PassRegistry::instance(),
                                    report, d));
            bool found = false;
            for (const auto& c : report.choices()) {
                if (c.strategy == tc.second) { found = true; }
            }
            VERIFY(found);
            // Both encodings are exact: the axis is size and solving time, not
            // fidelity, which is why the profile floors cannot separate them.
            VERIFY(report.fidelity().sound && report.fidelity().complete && report.fidelity().preserves_optimum && report.fidelity().bounds.empty() && report.fidelity().count_status == CountStatus::UNASSESSED);
        }
    }

    // A small shared DAG denotes an exponentially large expression tree.
    // Rewriting it must retain sharing and leave another owner's source model
    // unchanged, including when the global occurs under negative polarity.
    {
        auto model = modelWithAllDifferent(H::mkInt(0), H::mkInt(3));
        auto expression = H::mkOp(H::Op::NOT, {model.constraints.front().formula});
        constexpr int depth = 36;
        for (int i = 0; i < depth; ++i) {
            expression = H::mkOp(H::Op::AND, {expression, expression});
        }
        model.constraints.front().formula = expression;
        model.constraints.push_back(model.constraints.front());
        const auto original = model;
        const auto profile = EncodingProfile::builtin("ground");
        TranslationReport report;
        Diagnostics diagnostics;
        VERIFY(PassManager::run(model, *profile, PassRegistry::instance(), report, diagnostics));
        VERIFY(H::typeCheck(model, diagnostics));
        VERIFY(model.constraints[0].formula == model.constraints[1].formula);
        auto rewritten = model.constraints.front().formula;
        auto source = original.constraints.front().formula;
        for (int i = 0; i < depth; ++i) {
            VERIFY(rewritten->op == H::Op::AND && rewritten->args.size() == 2);
            VERIFY(rewritten->args[0] == rewritten->args[1]);
            rewritten = rewritten->args[0];
            source = source->args[0];
        }
        VERIFY(rewritten->op == H::Op::NOT);
        VERIFY(rewritten->args.front()->op == H::Op::DISTINCT);
        VERIFY(source->op == H::Op::NOT);
        VERIFY(source->args.front()->kind == H::ExprKind::GLOBAL);
    }

    std::cout << "alldifferent decomposes two ways, and the two differ.\n";
    return 0;
}
