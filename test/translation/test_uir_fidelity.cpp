// Fidelity lattice: meet must be commutative, associative and idempotent.
#include "somtparser/translation/fidelity.h"
#include <cassert>
#include <iostream>
#include <vector>
#include <algorithm>

using SOMTParser::Uir::Fidelity;

// Compare two bounds by content (kind, value, site).
static bool boundEqual(const Fidelity::Bound& a, const Fidelity::Bound& b) {
    return a.kind == b.kind && a.value == b.value && a.site == b.site;
}

// Check if two bounds vectors contain the same elements as multisets/sets.
static bool boundsEqual(const std::vector<Fidelity::Bound>& a,
                        const std::vector<Fidelity::Bound>& b) {
    if (a.size() != b.size()) return false;
    // Since meet produces unions, elements may be in different order.
    // Check that each element in a exists in b and vice versa.
    for (const auto& abound : a) {
        bool found = false;
        for (const auto& bbound : b) {
            if (boundEqual(abound, bbound)) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

static bool sameLattice(const Fidelity& a, const Fidelity& b) {
    return a.sound == b.sound
        && a.complete == b.complete
        && a.preserves_optimum == b.preserves_optimum
        // Count assessment is a tri-state coordinate, so comparing only the
        // compatibility Boolean would conflate unassessed and no-guarantee.
        && a.count_status == b.count_status
        && boundsEqual(a.bounds, b.bounds);
}

// Order-sensitive equality. sameLattice() deliberately compares bounds as
// sets, which is the right notion for the algebra -- but report.cpp serialises
// `bounds` in vector order, so two meets that are "the same lattice element"
// still produce different JSON if their vectors differ. The laws below are
// checked with sameLattice; this stricter relation is what the serialised
// report actually depends on, and it needs its own assertion.
static bool sameSerialisation(const Fidelity& a, const Fidelity& b) {
    if (a.bounds.size() != b.bounds.size()) return false;
    for (std::size_t i = 0; i < a.bounds.size(); ++i) {
        if (!boundEqual(a.bounds[i], b.bounds[i])) return false;
    }
    return true;
}

int main() {
    const Fidelity ex  = Fidelity::exact();
    const Fidelity eq  = Fidelity::equisat();
    const Fidelity un  = Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, 32, "x"});
    const Fidelity ov  = Fidelity::overApprox();

    // exact() is exact on the older axes, but does not assess count.
    assert(!ex.isExact());
    assert(ex.sound && ex.complete && ex.preserves_optimum && ex.bounds.empty());
    assert(ex.count_status == SOMTParser::Uir::CountStatus::UNASSESSED);
    Fidelity count_exact = Fidelity::exact();
    count_exact.count_status = SOMTParser::Uir::CountStatus::PRESERVED;
    assert(count_exact.isExact());

    // Under-approximation keeps SAT answers, loses UNSAT answers.
    assert(un.sound);
    assert(!un.complete);
    assert(un.bounds.size() == 1);
    assert(un.bounds[0].kind == Fidelity::Bound::BV_WIDTH);
    assert(un.bounds[0].value == 32);

    // Over-approximation is the mirror image.
    assert(!ov.sound);
    assert(ov.complete);
    assert(!ov.preserves_optimum);
    // ...and it carries no Bound. A Bound means "the conclusion holds only
    // within this limit", which is the under-approximation direction; an
    // over-approximation's UNSAT is globally valid, so a Bound here would
    // tell the eval pipeline -- which stratifies on this very field -- the
    // opposite of what happened.
    assert(ov.bounds.empty());
    assert(!ov.isExact());

    // The two are incomparable: meeting them loses both directions.
    const Fidelity both = Fidelity::meet(un, ov);
    assert(!both.sound && !both.complete);

    // The algebra loop below used to run over {ex, eq, un, ov}, of which
    // exactly one carries a bound -- so every meet in it unioned at most one
    // bound, and the bound-merging half of meet() was never exercised by any
    // law. These four make it non-trivial: distinct sites, distinct kinds,
    // duplicate bounds, and an element that already holds two.
    const Fidelity un_s = Fidelity::underApprox({Fidelity::Bound::BMC_DEPTH, 10, "sys"});
    const Fidelity un_x2 = Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, 64, "x"});
    const Fidelity un_dup = Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, 32, "x"});
    const Fidelity un_two = Fidelity::meet(un, un_s);

    const std::vector<Fidelity> all = {
        ex, count_exact, eq, un, ov, un_s, un_x2, un_dup, un_two};
    for (const auto& a : all) {
        // Idempotent.
        assert(sameLattice(Fidelity::meet(a, a), a));
        for (const auto& b : all) {
            // Commutative.
            assert(sameLattice(Fidelity::meet(a, b), Fidelity::meet(b, a)));
            // ...right down to the order of `bounds`. meet() used to seed the
            // result from its left argument and append the right's, so
            // meet(bv-width-on-x, bmc-depth-on-sys) produced [x, sys] and the
            // reverse produced [sys, x]; report.cpp writes them out in that
            // order, which made a translation's JSON depend on which pass ran
            // first. Commutativity that only holds up to reordering is not
            // enough when the order is the observable.
            assert(sameSerialisation(Fidelity::meet(a, b), Fidelity::meet(b, a)));
            for (const auto& c : all) {
                // Associative.
                assert(sameLattice(Fidelity::meet(Fidelity::meet(a, b), c),
                                   Fidelity::meet(a, Fidelity::meet(b, c))));
            }
        }
    }

    // An unknown stage blocks a positive composition claim, while an
    // explicit no-guarantee stage remains distinguishable from unknown.
    assert(Fidelity::meet(ex, count_exact).count_status
           == SOMTParser::Uir::CountStatus::UNASSESSED);
    assert(Fidelity::meet(count_exact, eq).count_status
           == SOMTParser::Uir::CountStatus::NO_GUARANTEE);

    // Bounds accumulate as a union, so provenance of every bound survives.
    const Fidelity two = Fidelity::meet(
        un, Fidelity::underApprox({Fidelity::Bound::BMC_DEPTH, 10, "sys"}));
    assert(two.bounds.size() == 2);
    assert(!two.isExact());

    // It is a union, not a concatenation: an identical bound arriving twice
    // stays one entry, so a pass re-run does not double-count its own limit.
    assert(Fidelity::meet(un, un_dup).bounds.size() == 1);
    // ...but "identical" means all three fields. Two BV_WIDTH bounds on the
    // same site with different widths are two different facts about the
    // translation and both must survive.
    assert(Fidelity::meet(un, un_x2).bounds.size() == 2);

    std::cout << "All Fidelity lattice tests passed." << std::endl;
    return 0;
}
