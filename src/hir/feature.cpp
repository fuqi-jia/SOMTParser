/* -*- Source -*-
 * Feature interning table.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/hir/feature.h"
#include "somtparser/core/asserting.h"

#include <deque>
#include <mutex>
#include <string>
#include <unordered_map>

namespace SOMTParser::Uir {

namespace {

struct InternTable {
    std::mutex                                    mu;
    std::deque<std::string>                       names;   // stable addresses
    std::unordered_map<std::string_view, std::uint32_t> index;
};

InternTable& table() {
    static InternTable t;
    return t;
}

} // namespace

Feature Feature::of(std::string_view name) {
    condAssert(!name.empty(), "Feature::of: empty feature name");
    InternTable& t = table();
    std::lock_guard<std::mutex> lock(t.mu);
    auto it = t.index.find(name);
    if (it != t.index.end()) {
        return Feature(it->second);
    }
    t.names.emplace_back(name);
    const auto id = static_cast<std::uint32_t>(t.names.size() - 1);
    // Key into the stored copy so the view stays valid for the process lifetime.
    t.index.emplace(std::string_view(t.names.back()), id);
    return Feature(id);
}

std::string_view Feature::name() const {
    InternTable& t = table();
    std::lock_guard<std::mutex> lock(t.mu);
    // An empty view here would be worse than a throw: PassTraits matches
    // features by name, so a silently-empty name would match nothing and let
    // a misordered pass pipeline through the very check meant to stop it.
    condAssert(id_ < t.names.size(), "Feature::name: id is out of range");
    return t.names[id_];
}

// Only four of these can be produced by ConstraintModel::features() today:
// int-var, real-var, soft-constraint and nonlinear. The other nine name
// constructs the HIR cannot yet represent, so a pass declaring requires_absent
// on one of them passes PassManager::validate for every possible input --
// vacuously, not because the pipeline is sound. test/translation/
// test_uir_feature_reachability.cpp pins that partition and fails if a feature
// is added here without being classified, so the gap stays visible until the
// HIR closes it.
namespace feat {
Feature comprehension()    { return Feature::of("comprehension"); }
Feature set()              { return Feature::of("set"); }
Feature globalConstraint() { return Feature::of("global-constraint"); }
Feature reification()      { return Feature::of("reification"); }
Feature intVar()           { return Feature::of("int-var"); }
Feature realVar()          { return Feature::of("real-var"); }
Feature optionalVar()      { return Feature::of("optional-var"); }
Feature enumType()         { return Feature::of("enum-type"); }
Feature softConstraint()   { return Feature::of("soft-constraint"); }
Feature quantifier()       { return Feature::of("quantifier"); }
Feature nonlinear()        { return Feature::of("nonlinear"); }
Feature transitionSystem() { return Feature::of("transition-system"); }
Feature hornClause()       { return Feature::of("horn-clause"); }
} // namespace feat

} // namespace SOMTParser::Uir
