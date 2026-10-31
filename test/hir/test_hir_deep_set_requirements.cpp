#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <vector>

namespace H = SOMTParser::Uir::Hir;

int main() {
    constexpr std::size_t depth = 200000;
    const auto check = [&](bool with_set_binder) {
        H::ConstraintModel model;
        H::ExprPtr leaf = with_set_binder
            ? H::mkForall({H::Binder{"s", H::Sort::set(H::Sort::integer())}}, H::mkBool(true))
            : H::mkBool(true);
        std::vector<H::ExprPtr> nodes{leaf};
        for (std::size_t i = 0; i < depth; ++i) {
            nodes.push_back(H::mkOp(H::Op::NOT, {nodes.back()}));
        }
        model.constraints.push_back({nodes.back()});
        model.constraints.push_back({nodes.back()}); // Shared source, one visit.
        const auto requirements = model.setSolverRequirements();
        VERIFY(requirements.has_sets == with_set_binder);
        VERIFY(requirements.has_quantifiers == with_set_binder);
        VERIFY(requirements.infinite_or_unknown_carrier == with_set_binder);
        VERIFY(!requirements.non_integer_carrier);
        VERIFY(model.constraints[0].formula == nodes.back());
        VERIFY(model.constraints[0].formula == model.constraints[1].formula);
        model.constraints.clear();
        // Isolate requirement traversal from recursive shared_ptr teardown.
        for (auto it = nodes.rbegin(); it != nodes.rend(); ++it) { it->reset(); }
    };
    check(false);
    check(true);
    return 0;
}
