// Feature is an interned string: adding a language must not force a core rebuild.
#include "somtparser/hir/feature.h"
#include <cassert>
#include <iostream>
#include <string>
#include <unordered_set>

using SOMTParser::Uir::Feature;
namespace feat = SOMTParser::Uir::feat;

int main() {
    // Interning: same spelling, same identity, regardless of route.
    const Feature a = Feature::of("int-var");
    const Feature b = Feature::of(std::string("int-var"));
    assert(a == b);
    assert(a.name() == "int-var");

    const Feature other = Feature::of("set");
    assert(!(a == other));
    assert(a != other);

    // Built-in constants are ordinary interned features.
    assert(feat::intVar() == Feature::of("int-var"));
    assert(feat::globalConstraint().name() == "global-constraint");
    assert(feat::transitionSystem() != feat::hornClause());

    // Usable as a hash key, which PassTraits relies on.
    std::unordered_set<Feature, Feature::Hash> s;
    s.insert(feat::intVar());
    s.insert(Feature::of("int-var"));
    s.insert(feat::set());
    assert(s.size() == 2);
    assert(s.count(Feature::of("int-var")) == 1);

    // A language may mint a feature the core never heard of.
    const Feature custom = Feature::of("cryptoline-modular-assertion");
    assert(custom.name() == "cryptoline-modular-assertion");
    assert(custom == Feature::of("cryptoline-modular-assertion"));

    std::cout << "All Feature interning tests passed." << std::endl;
    return 0;
}
