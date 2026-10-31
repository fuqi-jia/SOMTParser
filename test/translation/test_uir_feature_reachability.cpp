// Which features can ConstraintModel::features() actually report?
//
// PassManager::validate builds its `present` set from features() and rejects a
// profile whose pass declares `requires_absent` on something still in it.
// pass.h calls that check "the main reason this design has a pass pipeline at
// all". It is also, for most features, structurally incapable of failing:
// features() inspects declaration sorts, the soft flag and multiplication, so
// it can only ever produce four of the thirteen names in feat::. A pass
// declaring requires_absent = {globalConstraint()} validates against every
// possible input, and would keep doing so while quietly miscompiling the first
// frontend that produces global constraints.
//
// That is not wrong today -- the HIR cannot represent a set, a comprehension, a
// quantifier or a transition system, so no frontend can produce one -- and the
// fix is not to make features() lie. The fix is to make the gap visible and
// keep it that way: this file pins both halves of the partition. Teaching the
// HIR to represent one of the reserved constructs makes this test fail, which
// is the reminder to teach features() about it in the same change.

#include "somtparser/hir/hir.h"
#include "somtparser/translation/pass.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <string>
#include <vector>

using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace {

/** Every name in `namespace feat` (src/hir/feature.cpp). Adding one there
 *  without adding it here leaves it unclassified, which is the state this
 *  file exists to prevent. */
const std::vector<std::pair<Feature, const char*>>& allFeatures() {
    static const std::vector<std::pair<Feature, const char*>> kAll = {
        {feat::comprehension(),    "comprehension"},
        {feat::set(),              "set"},
        {feat::globalConstraint(), "global-constraint"},
        {feat::reification(),      "reification"},
        {feat::intVar(),           "int-var"},
        {feat::realVar(),          "real-var"},
        {feat::optionalVar(),      "optional-var"},
        {feat::enumType(),         "enum-type"},
        {feat::softConstraint(),   "soft-constraint"},
        {feat::quantifier(),       "quantifier"},
        {feat::nonlinear(),        "nonlinear"},
        {feat::transitionSystem(), "transition-system"},
        {feat::hornClause(),       "horn-clause"},
    };
    return kAll;
}

/** The four features today's HIR can express, each paired with a model that
 *  expresses it. A feature in this list that features() does not report is a
 *  detection bug; one it reports that is *not* in this list is a feature the
 *  reserved half below no longer covers. */
std::vector<std::pair<Feature, ConstraintModel>> representable() {
    std::vector<std::pair<Feature, ConstraintModel>> out;

    {
        ConstraintModel m;
        VarDecl d;
        d.name = "x";
        d.sort = Sort::integer();
        m.decls.push_back(d);
        out.emplace_back(feat::intVar(), m);
    }
    {
        ConstraintModel m;
        VarDecl d;
        d.name = "r";
        d.sort = Sort::real();
        m.decls.push_back(d);
        out.emplace_back(feat::realVar(), m);
    }
    {
        ConstraintModel m;
        Constraint c;
        c.formula = mkBool(true);
        c.soft = true;
        c.weight = 3;
        m.constraints.push_back(c);
        out.emplace_back(feat::softConstraint(), m);
    }
    {
        // Two non-constant factors is what makes a product nonlinear; x * 2 is
        // not, and the detector has to tell them apart.
        ConstraintModel m;
        VarDecl d;
        d.name = "x";
        d.sort = Sort::integer();
        m.decls.push_back(d);
        VarDecl e;
        e.name = "y";
        e.sort = Sort::integer();
        m.decls.push_back(e);
        Constraint c;
        c.formula = mkOp(Op::GT,
                         {mkOp(Op::MUL, {mkIdent("x", Sort::integer()),
                                         mkIdent("y", Sort::integer())}),
                          mkInt(0)});
        m.constraints.push_back(c);
        out.emplace_back(feat::nonlinear(), m);
    }
    {
        // A global constraint. Reachable since decompose-globals landed: before
        // that, ExprKind::GLOBAL did not exist and this feature was one of the
        // nine nothing could produce.
        ConstraintModel m;
        VarDecl a;
        a.name = "a";
        a.sort = Sort::array(Sort::integer(), Sort::integer());
        m.decls.push_back(a);
        Constraint c;
        c.formula = mkGlobal("alldifferent",
                             {mkIdent("a", a.sort), mkInt(0), mkInt(3)});
        m.constraints.push_back(c);
        out.emplace_back(feat::globalConstraint(), m);
    }
    {
        // A quantifier. Reachable for the same reason -- and note that
        // PassManager::validate erases it rather than demanding a pass, because
        // SMT-LIB expresses quantifiers natively (cluster C's "no new pass").
        ConstraintModel m;
        VarDecl x;
        x.name = "x";
        x.sort = Sort::integer();
        m.decls.push_back(x);
        Constraint c;
        Binder b{"i", Sort::integer()};
        c.formula = mkForall({b}, mkOp(Op::LE, {mkBoundVar("i", Sort::integer()),
                                                mkIdent("x", Sort::integer())}));
        m.constraints.push_back(c);
        out.emplace_back(feat::quantifier(), m);
    }
    return out;
}

bool has(const std::unordered_set<Feature, Feature::Hash>& s, Feature f) {
    return s.count(f) != 0;
}

} // namespace

int main() {
    std::cout << "======= Feature reachability =======\n";

    const auto reps = representable();

    // ---- Every representable feature is really detected. --------------------
    for (const auto& [f, m] : reps) {
        const auto found = m.features();
        assert(has(found, f));
    }

    // ---- Nonlinearity is detected, and only where it exists. ----------------
    {
        ConstraintModel m;
        VarDecl d;
        d.name = "x";
        d.sort = Sort::integer();
        m.decls.push_back(d);
        Constraint c;
        c.formula = mkOp(Op::GT, {mkOp(Op::MUL, {mkInt(2), mkIdent("x", Sort::integer())}),
                                  mkInt(0)});
        m.constraints.push_back(c);
        assert(!has(m.features(), feat::nonlinear()));
    }

    // ---- The reserved half. -------------------------------------------------
    // For each feature not in the representable list, no model built out of the
    // representable ones -- nor their union -- can produce it. That is the
    // property that makes requires_absent on it vacuous.
    ConstraintModel everything;
    for (const auto& [f, m] : reps) {
        (void)f;
        everything.decls.insert(everything.decls.end(), m.decls.begin(), m.decls.end());
        everything.constraints.insert(everything.constraints.end(),
                                      m.constraints.begin(), m.constraints.end());
    }
    // The union declares x twice; features() does not care, and this file is
    // about feature detection, not about well-sortedness (see
    // test_uir_typecheck.cpp for that).
    const auto from_everything = everything.features();

    std::vector<std::string> reserved;
    for (const auto& [f, name] : allFeatures()) {
        const bool is_representable =
            std::any_of(reps.begin(), reps.end(),
                        [f = f](const auto& kv) { return kv.first == f; });
        if (is_representable) {
            assert(has(from_everything, f));
            continue;
        }
        // Not merely absent from this model: unreachable, because the HIR has
        // no way to write one down. When that stops being true, move the
        // feature into representable() and give it a model.
        assert(!has(from_everything, f));
        reserved.push_back(name);
    }

    // The count is asserted, not just the membership: a feature added to
    // feat:: but forgotten here would otherwise slip through unclassified.
    assert(reps.size() == 6);
    assert(reserved.size() == 7);
    assert(reps.size() + reserved.size() == allFeatures().size());

    std::cout << reps.size() << " feature(s) the HIR can express, "
              << reserved.size() << " reserved for a future HIR:\n  ";
    for (const auto& r : reserved) { std::cout << r << ' '; }
    std::cout << "\n";
    std::cout
        << "A pass declaring requires_absent on any reserved feature validates\n"
           "for every possible input today. That is safe only while the HIR\n"
           "cannot express it; see this file's header.\n";

    std::cout << "All feature reachability tests passed." << std::endl;
    return 0;
}
