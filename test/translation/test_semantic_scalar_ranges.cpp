#include "somtparser/translation/semantics.h"
#include "test_helpers.h"

#include <algorithm>
#include <functional>
#include <limits>
#include <stdexcept>

using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;
namespace S = SOMTParser::Uir::Sem;

static H::ConstraintModel modelWithRanges(std::uint64_t count) {
    H::ConstraintModel model;
    model.bool_var_ranges.push_back({"b", 1, 2});
    model.scalar_var_ranges.push_back({"pos[7][", 0, count, H::Sort::integer(),
        {"ranges.xml", 17, 3}, "]", H::mkInt(-2), H::mkInt(5)});
    return model;
}

static S::TranslationContract frontend(const H::ConstraintModel& model) {
    return S::xcsp3ToRelationalContract(model, Fidelity::exact());
}

int main() {
    const auto large = modelWithRanges(1000000000ULL);
    const auto source = frontend(large);
    VERIFY(source.target_signature.symbols.empty());
    VERIFY(source.target_signature.symbol_ranges.size() == 2);
    VERIFY(source.target_axioms.empty());
    VERIFY(source.target_range_axioms.size() == 1);
    VERIFY(source.target_range_axioms[0].lower_bound == large.scalar_var_ranges[0].lower_bound);
    VERIFY(source.target_range_axioms[0].loc.line == 17);
    VERIFY(source.projection.observable_ranges.size() == 2);
    VERIFY(source.symbol_range_map[1].source_suffix == "]");
    VERIFY(source.symbol_range_map[1].target_suffix == "]");
    VERIFY(source.target_signature.symbol_ranges[1].name(9) == "pos[7][9]");
    Diagnostics diagnostics;
    VERIFY(source.validate(diagnostics));
    S::TranslationPipeline large_pipeline;
    large_pipeline.add(source);
    large_pipeline.add(S::relationalToSmtContract(large, false));
    VERIFY(large_pipeline.validate(diagnostics));
    VERIFY(!diagnostics.hasErrors());

    const auto reject = [&](const std::function<void(S::TranslationContract&)>& mutate) {
        auto changed = source;
        mutate(changed);
        Diagnostics errors;
        VERIFY(!changed.validate(errors));
        VERIFY(errors.hasErrors());
    };
    reject([](auto& c) { c.symbol_range_map[1].source_suffix.clear(); });
    reject([](auto& c) { c.symbol_range_map[1].target_suffix.clear(); });
    reject([](auto& c) { c.projection.observable_ranges[1].target_suffix.clear(); });
    reject([](auto& c) { c.projection.observable_ranges[1].source_suffix.clear(); });
    reject([](auto& c) { c.symbol_range_map.push_back(c.symbol_range_map[1]); });
    reject([](auto& c) { c.projection.observable_ranges.push_back(c.projection.observable_ranges[1]); });
    reject([](auto& c) { c.target_range_axioms[0].lower_bound = H::mkBool(false); });
    reject([](auto& c) { c.target_range_axioms[0].upper_bound = H::mkReal("5.5"); });
    reject([](auto& c) { c.target_range_axioms[0].suffix.clear(); });
    reject([](auto& c) { c.target_range_axioms[0].count = 0; });
    reject([](auto& c) { --c.target_range_axioms[0].count; });
    reject([](auto& c) { c.target_range_axioms[0].first = std::numeric_limits<std::uint64_t>::max(); });

    auto signature = source.target_signature.materialize();
    signature.symbol_ranges[1].suffix = "]extra";
    VERIFY(!S::signatureMatchesModel(S::SignatureSnapshot(signature), large));
    VERIFY(S::signatureMatchesModel(source.target_signature, large));
    // Endpoints and suffixes are part of each interface, even when both
    // stages are separately well-formed and have the same symbol count.
    auto unbounded = large;
    unbounded.scalar_var_ranges[0].lower_bound.reset();
    unbounded.scalar_var_ranges[0].upper_bound.reset();
    auto changed_names = unbounded;
    changed_names.scalar_var_ranges[0].suffix = "]extra";
    S::TranslationPipeline mismatch;
    mismatch.add(frontend(unbounded));
    auto changed_backend = S::relationalToSmtContract(changed_names, false);
    VERIFY(changed_backend.validate(diagnostics));
    mismatch.add(std::move(changed_backend));
    Diagnostics mismatch_errors;
    VERIFY(!mismatch.validate(mismatch_errors));

    // Removing an auxiliary function must retain both compact families in
    // the source signature. This used to drop all ranges during filtering.
    auto with_helper = large;
    H::FunDecl helper;
    helper.name = "helper";
    helper.result = H::Sort::integer();
    helper.body = H::mkInt(4);
    helper.auxiliary = true;
    with_helper.funs.push_back(helper);
    const auto filtered = frontend(with_helper);
    VERIFY(filtered.source_signature.symbols.empty());
    VERIFY(filtered.source_signature.symbol_ranges.size() == 2);
    VERIFY(filtered.validate(diagnostics));

    // A real assignment travels through the two beta maps using the exact
    // original array coordinate names, including brackets and row index.
    const auto small = modelWithRanges(3);
    const auto first = frontend(small);
    S::TranslationPipeline pipeline;
    pipeline.add(first);
    pipeline.add(S::relationalToSmtContract(small, false, first.projection));
    VERIFY(pipeline.validate(diagnostics));
    const S::Assignment values{{"b1", "true"}, {"b2", "false"},
        {"pos[7][0]", "-2"}, {"pos[7][1]", "5"}, {"pos[7][2]", "0"}};
    S::Assignment projected;
    VERIFY(pipeline.project(values, projected, diagnostics));
    VERIFY(projected == values);
    auto missing = values;
    missing.erase("pos[7][1]");
    Diagnostics missing_errors;
    VERIFY(!pipeline.project(missing, projected, missing_errors));

    S::ModelProjection renamed;
    renamed.observable_ranges.push_back({"pos[7][", "target(", 0, 10, 3,
        S::ProjectionKind::DIRECT, "]", ")"});
    VERIFY(renamed.project({{"target(10)", "-2"}, {"target(11)", "5"},
                            {"target(12)", "0"}}, projected, diagnostics));
    VERIFY(projected.size() == 3 && projected.at("pos[7][1]") == "5");
    VERIFY(!diagnostics.hasErrors());
    return 0;
}
