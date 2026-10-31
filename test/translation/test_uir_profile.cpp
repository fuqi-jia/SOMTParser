// An encoding profile is a pass pipeline plus a fidelity floor. "Strict mode"
// is a profile, not a flag, so strict/default/aggressive are three points on
// one experimental axis instead of an orthogonal switch.
#include "somtparser/translation/profile.h"
#include <algorithm>
#include <cassert>
#include <iostream>
#include <string>
#include <vector>

using namespace SOMTParser::Uir;

int main() {
    // Built-ins the CLI and the evaluation refer to by name.
    const auto ids = EncodingProfile::builtinIds();
    assert(ids.size() >= 3);
    bool has_default = false, has_strict = false, has_bv32 = false;
    bool has_feasibility = false;
    for (const auto& s : ids) {
        if (s == "default") has_default = true;
        if (s == "strict")  has_strict = true;
        if (s == "bv32")    has_bv32 = true;
        if (s == "feasibility") has_feasibility = true;
    }
    assert(has_default && has_strict && has_bv32 && has_feasibility);

    const auto def = EncodingProfile::builtin("default");
    assert(def != nullptr);
    assert(def->id() == "default");
    // The default floor demands both directions: no silent approximation.
    assert(def->minFidelity().sound);
    assert(def->minFidelity().complete);

    // strict is the same floor expressed as a profile, with no lossy passes.
    const auto strict = EncodingProfile::builtin("strict");
    assert(strict != nullptr);
    assert(strict->minFidelity().sound && strict->minFidelity().complete);

    // Plain SMT can preserve an optimization problem's feasible set without
    // preserving its optimum. That weakening is an explicit profile, not a
    // silent side effect of selecting the `none` output dialect.
    const auto feasibility = EncodingProfile::builtin("feasibility");
    assert(feasibility != nullptr);
    assert(feasibility->minFidelity().sound);
    assert(feasibility->minFidelity().complete);
    assert(!feasibility->minFidelity().preserves_optimum);

    // bv32 deliberately relaxes completeness, because a fixed width loses
    // solutions outside it. Despite its name it runs "bound-ints", not a real
    // int-to-bv pass (that needs a BV Sort in HIR -- Plan 6's scope): it
    // clamps the Int domain instead of changing its sort.
    const auto bv32 = EncodingProfile::builtin("bv32");
    assert(bv32 != nullptr);
    assert(bv32->minFidelity().sound);
    assert(!bv32->minFidelity().complete);
    assert(!bv32->pipeline().empty());
    // Found by id, not by position. These assertions are about the bound-ints
    // SPEC's parameters; the position is a separate claim, asserted on its own
    // below, and indexing by 0 here silently conflated the two -- it broke when
    // a second pass joined the pipeline, for a reason that had nothing to do
    // with what any of these four lines is checking.
    const PassSpec* bi = nullptr;
    for (const PassSpec& s : bv32->pipeline()) {
        if (s.pass_id == "bound-ints") { bi = &s; }
    }
    assert(bi != nullptr);
    assert(bi->intParam("width", 0) == 32);
    assert(bi->param("missing", "fallback") == "fallback");
    assert(bi->intParam("missing", 7) == 7);

    // Unknown names fail rather than silently falling back to default, which
    // would make an experiment row lie about which profile produced it.
    assert(EncodingProfile::builtin("no-such-profile") == nullptr);

    // The hash is stable across calls and distinguishes different pipelines:
    // it goes into Provenance so a result row can be traced to a configuration.
    assert(def->contentHash() == EncodingProfile::builtin("default")->contentHash());
    assert(def->contentHash() != bv32->contentHash());
    assert(def->contentHash().size() == 16);

    // Two profiles differing only in a parameter must hash differently.
    const auto a = EncodingProfile::make(
        "a", {PassSpec{"int-to-bv", {{"width", "32"}}}}, Fidelity::exact());
    const auto b = EncodingProfile::make(
        "a", {PassSpec{"int-to-bv", {{"width", "64"}}}}, Fidelity::exact());
    assert(a->contentHash() != b->contentHash());

    // Test error paths in intParam: malformed values must throw, not silently fall back.
    // This is the safety-critical behavior that ensures profile typos don't run under
    // the wrong encoding while the report lies about it.

    // Case 1: Unparseable value should throw std::runtime_error.
    const auto bad_abc = PassSpec{"int-to-bv", {{"width", "abc"}}};
    try {
        bad_abc.intParam("width", 32);
        assert(false && "unparseable value should have thrown");
    } catch (const std::runtime_error& e) {
        assert(std::string(e.what()).find("width") != std::string::npos);
        assert(std::string(e.what()).find("abc") != std::string::npos);
    }

    // Case 2: Trailing characters should throw (std::stoll accepts "32x" as 32, but
    // the consumed-length check rejects it—this is the whole point of that check).
    const auto bad_trailing = PassSpec{"int-to-bv", {{"width", "32x"}}};
    try {
        bad_trailing.intParam("width", 0);
        assert(false && "trailing characters should have thrown");
    } catch (const std::runtime_error& e) {
        assert(std::string(e.what()).find("width") != std::string::npos);
        assert(std::string(e.what()).find("32x") != std::string::npos);
    }

    // Case 3: Empty string is present but malformed, should throw.
    const auto bad_empty = PassSpec{"int-to-bv", {{"width", ""}}};
    try {
        bad_empty.intParam("width", 16);
        assert(false && "empty value should have thrown");
    } catch (const std::runtime_error& e) {
        assert(std::string(e.what()).find("width") != std::string::npos);
    }

    // Case 4: Absent key legitimately falls back to default (not an error).
    const auto good_absent = PassSpec{"int-to-bv", {}};
    assert(good_absent.intParam("width", 16) == 16);

    // Case 5: Clean value parses correctly without throwing.
    const auto good_clean = PassSpec{"int-to-bv", {{"width", "32"}}};
    assert(good_clean.intParam("width", 0) == 32);

    // ---- The two encoding-style profiles. -----------------------------------
    {
        const auto ground = EncodingProfile::builtin("ground");
        const auto quant  = EncodingProfile::builtin("quantified");
        assert(ground && quant);
        assert(ground->style() == EncodingStyle::GROUND);
        assert(quant->style() == EncodingStyle::QUANTIFIED);

        // Their floors require the old guarantees but do not require count
        // preservation; count status is a separate question axis.
        //
        // Neither is isExact() any more: no built-in profile floor demands
        // count preservation (an encoding fit for a satisfiability or
        // optimisation query need not preserve the model count -- see
        // profile.cpp's makeDefault()), so isExact() would now be false here
        // for a reason unrelated to what this assertion checks. Name the
        // three flags it used to stand in for instead.
        assert(ground->minFidelity().sound && ground->minFidelity().complete
               && ground->minFidelity().preserves_optimum
               && ground->minFidelity().bounds.empty());
        assert(ground->minFidelity().count_status == CountStatus::UNASSESSED);
        assert(quant->minFidelity().sound && quant->minFidelity().complete
               && quant->minFidelity().preserves_optimum
               && quant->minFidelity().bounds.empty());
        assert(quant->minFidelity().count_status == CountStatus::UNASSESSED);

        // The hash must separate them, and the style is the only thing that
        // does: both run the *same* pipeline -- decompose-globals -- and differ
        // only in the style it reads. Leave the style out of the digest and a
        // result row could not say which encoding produced it.
        assert(ground->contentHash() != quant->contentHash());
        assert(ground->pipeline().size() == 1);
        assert(quant->pipeline().size() == 1);
        assert(ground->pipeline()[0].pass_id == "decompose-globals");
        assert(quant->pipeline()[0].pass_id == ground->pipeline()[0].pass_id);

        // The style is genuinely in the digest, not just the id: two profiles
        // differing only in style must differ in hash.
        const auto a = EncodingProfile::make("same", {}, Fidelity::exact(),
                                             EncodingStyle::GROUND);
        const auto b = EncodingProfile::make("same", {}, Fidelity::exact(),
                                             EncodingStyle::QUANTIFIED);
        assert(a->contentHash() != b->contentHash());

        // A profile that takes no position still hashes differently from both.
        const auto u = EncodingProfile::make("same", {}, Fidelity::exact());
        assert(u->style() == EncodingStyle::UNSPECIFIED);
        assert(u->contentHash() != a->contentHash());
        assert(u->contentHash() != b->contentHash());

        // Both are listed, so --list-profiles and the Python profiles() see them.
        const auto ids = EncodingProfile::builtinIds();
        assert(std::find(ids.begin(), ids.end(), "ground") != ids.end());
        assert(std::find(ids.begin(), ids.end(), "quantified") != ids.end());

        // `default` and `strict` DO face the question, since 2026-08-16: they
        // run decompose-globals, because leaving them empty meant every model
        // containing a global constraint was refused by the profile the CLI
        // uses when given no flag. Taking no position was correct only while
        // nothing in the pipeline asked; the assertion that they take none
        // outlived that by exactly as long as it took to notice.
        assert(EncodingProfile::builtin("default")->style()
               == EncodingStyle::GROUND);
        assert(EncodingProfile::builtin("strict")->style()
               == EncodingStyle::GROUND);
        assert(EncodingProfile::builtin("default")->pipeline().size() == 1);
        assert(EncodingProfile::builtin("default")->pipeline()[0].pass_id
               == "decompose-globals");
        // Default/strict do not require count preservation. This keeps their
        // historic floor behavior without making a claim about actual count.
        assert(EncodingProfile::builtin("default")->minFidelity().sound
               && EncodingProfile::builtin("default")->minFidelity().complete
               && EncodingProfile::builtin("default")->minFidelity().preserves_optimum
               && EncodingProfile::builtin("default")->minFidelity().bounds.empty());
        assert(EncodingProfile::builtin("default")->minFidelity().count_status
               == CountStatus::UNASSESSED);
        assert(EncodingProfile::builtin("strict")->minFidelity().sound
               && EncodingProfile::builtin("strict")->minFidelity().complete
               && EncodingProfile::builtin("strict")->minFidelity().preserves_optimum
               && EncodingProfile::builtin("strict")->minFidelity().bounds.empty());
        assert(EncodingProfile::builtin("strict")->minFidelity().count_status
               == CountStatus::UNASSESSED);

        // bv32 and bmc decompose too, since 2026-08-17. They were left alone
        // one round longer on the reasoning that a narrower profile's scope is
        // its own business -- but an empty pipeline does not DECLINE to encode
        // a global constraint, it refuses the model, and a profile says what it
        // will not preserve through its fidelity floor, not by omitting a pass.
        // Every built-in profile now takes a position on the encoding style.
        for (const std::string& id : EncodingProfile::builtinIds()) {
            const auto p = EncodingProfile::builtin(id);
            assert(p != nullptr);
            assert(p->style() != EncodingStyle::UNSPECIFIED);
            bool decomposes = false;
            for (const PassSpec& s : p->pipeline()) {
                if (s.pass_id == "decompose-globals") { decomposes = true; }
            }
            assert(decomposes);
        }
        // bv32 runs BOTH, and decompose-globals is first. The two commute
        // today -- bound-ints walks decls and the ground decomposition adds
        // none -- so this pins the order against the encoding that does
        // introduce variables, which would otherwise be left unclamped while
        // the report still recorded a width bound over them.
        {
            const auto bv32 = EncodingProfile::builtin("bv32");
            assert(bv32->pipeline().size() == 2);
            assert(bv32->pipeline()[0].pass_id == "decompose-globals");
            assert(bv32->pipeline()[1].pass_id == "bound-ints");
        }
        // The floors are untouched: decomposition is exact, so a profile that
        // gained one did not become more approximate.
        assert(!EncodingProfile::builtin("bv32")->minFidelity().isExact());
        assert(!EncodingProfile::builtin("bmc")->minFidelity().isExact());

        // Names are stable strings the evaluation groups by.
        assert(std::string(encodingStyleName(EncodingStyle::GROUND)) == "ground");
        assert(std::string(encodingStyleName(EncodingStyle::QUANTIFIED)) == "quantified");
        assert(std::string(encodingStyleName(EncodingStyle::UNSPECIFIED)) == "unspecified");
    }

    std::cout << "All EncodingProfile tests passed." << std::endl;
    return 0;
}
