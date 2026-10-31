// `preserves_count`: an encoding can preserve satisfiability perfectly and
// still change how many models there are.
//
// `sound`/`complete` are not this axis and `preserves_optimum` is not either --
// optimisation asks for an extremum over the model set, counting asks for its
// cardinality, and an encoding can keep one while destroying the other. The
// case that forced the axis is real and in this tree: the OPB WBO relaxation
// uses a ONE-SIDED implication, so a relaxation variable is free whenever its
// soft constraint holds and the model count is multiplied by 2^k.

#include "somtparser/translation/fidelity.h"
#include "somtparser/translation/profile.h"

#include <iostream>

#include "test_helpers.h"

using SOMTParser::Uir::Fidelity;

int main() {
    std::cout << "======= Fidelity: the counting axis =======\n";

    // Count is a separate evidence claim, not inherited from the other axes.
    VERIFY(Fidelity{}.count_status == SOMTParser::Uir::CountStatus::UNASSESSED);
    VERIFY(Fidelity::exact().count_status == SOMTParser::Uir::CountStatus::UNASSESSED);
    VERIFY(!Fidelity::exact().preservesCount());

    // `equisat()` promises equisatisfiability and NOTHING MORE. A constructor
    // must not grant a guarantee its name does not make -- and neither caller
    // preserves the count: the OPB WBO relaxation multiplies it by 2^k, and
    // the XCSP3 circuit encoding by the size of the circuit.
    VERIFY(Fidelity::equisat().count_status == SOMTParser::Uir::CountStatus::NO_GUARANTEE);

    // An under-approximation turns infinitely many models into finitely many
    // (`bound-ints` bounding an unbounded Int), and an over-approximation
    // admits models the source does not have.
    VERIFY(Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, 32, "x"}).count_status
           == SOMTParser::Uir::CountStatus::NO_GUARANTEE);
    VERIFY(Fidelity::overApprox().count_status
           == SOMTParser::Uir::CountStatus::NO_GUARANTEE);

    // The meet is field-wise, so one count-destroying step in a pipeline is
    // enough. This is the property the lattice exists for.
    {
        const Fidelity lost = Fidelity::meet(Fidelity::exact(), Fidelity::equisat());
        VERIFY(lost.count_status == SOMTParser::Uir::CountStatus::NO_GUARANTEE);
        VERIFY(lost.sound);          // and it costs nothing on the other axes
        VERIFY(lost.complete);
    }

    // `isExact()` means every guarantee, so it must include this one --
    // otherwise a count-destroying encoding reports as exact.
    {
        Fidelity f;
        f.count_status = SOMTParser::Uir::CountStatus::NO_GUARANTEE;
        VERIFY(!f.isExact());
    }

    // A floor that does not demand count preservation accepts a fidelity that
    // lacks it; one that demands it does not. `meets()` is what a profile
    // uses, so getting this backwards would admit the wrong models silently.
    {
        Fidelity lacks;
        lacks.count_status = SOMTParser::Uir::CountStatus::NO_GUARANTEE;
        Fidelity floor_without;
        VERIFY(lacks.meets(floor_without));
        Fidelity count_required;
        count_required.count_status = SOMTParser::Uir::CountStatus::PRESERVED;
        VERIFY(!lacks.meets(count_required));
        Fidelity count_preserved;
        count_preserved.count_status = SOMTParser::Uir::CountStatus::PRESERVED;
        VERIFY(count_preserved.meets(count_required));
    }

    // The profile digest encodes the floor's flags positionally, so adding a
    // bit changes every digest. That is a visible change to recorded
    // provenance, and it is pinned here so nobody reorders the bits later: a
    // digest whose meaning shifted silently would make two runs look like they
    // used different profiles when they did not.
    //
    // contentHash() is an FNV-1a hash, not the readable pre-hash string, so
    // the bit's position cannot be read off it directly the way an earlier
    // draft of this test assumed. Pin it the way that survives the hash being
    // opaque instead: two floors with the SAME NUMBER of flags false, but in
    // different positions, must still hash differently -- if position did not
    // matter, only the count of false flags would, and these would collide.
    {
        using SOMTParser::Uir::EncodingProfile;
        using SOMTParser::Uir::EncodingStyle;

        const auto default_profile = EncodingProfile::builtin("default");
        const auto bmc = EncodingProfile::builtin("bmc");
        VERIFY(default_profile != nullptr);
        VERIFY(bmc != nullptr);
        // No built-in profile floor demands count preservation. Its status is
        // an unassessed requirement, not a claim about the translation.
        VERIFY(default_profile->minFidelity().count_status
               == SOMTParser::Uir::CountStatus::UNASSESSED);
        VERIFY(default_profile->contentHash() != bmc->contentHash());

        Fidelity optimum_only_false = Fidelity::exact();
        optimum_only_false.preserves_optimum = false;
        Fidelity count_unassessed = Fidelity::exact();
        Fidelity count_no_guarantee = Fidelity::exact();
        count_no_guarantee.count_status = SOMTParser::Uir::CountStatus::NO_GUARANTEE;
        const auto p_optimum = EncodingProfile::make(
            "probe", {}, optimum_only_false, EncodingStyle::GROUND);
        const auto p_count = EncodingProfile::make(
            "probe", {}, count_no_guarantee, EncodingStyle::GROUND);
        VERIFY(p_optimum->contentHash() != p_count->contentHash());

        // And the new bit is really IN the digest, not decorative: flipping
        // only preserves_count on an otherwise-exact floor changes the hash.
        const auto p_exact = EncodingProfile::make(
            "probe", {}, Fidelity::exact(), EncodingStyle::GROUND);
        const auto p_unassessed = EncodingProfile::make(
            "probe", {}, count_unassessed, EncodingStyle::GROUND);
        VERIFY(p_unassessed->contentHash() != p_count->contentHash());
    }

    std::cout << "All Fidelity counting tests passed.\n";
    return 0;
}
