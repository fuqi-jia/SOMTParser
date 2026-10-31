#include "somtparser/translation/semantics.h"
#include "test_helpers.h"

#include <memory>

namespace H = SOMTParser::Uir::Hir;
namespace S = SOMTParser::Uir::Sem;

namespace {

bool isTotal(const S::RelationalBuilder& builder, const H::ExprPtr& value) {
    const auto defined = builder.inspect(value).defined;
    return defined && defined->kind == H::ExprKind::LIT_BOOL && defined->bool_value;
}

} // namespace

int main() {
    S::RelationalBuilder builder;
    const auto guard = H::mkIdent("guard", H::Sort::boolean());
    const auto second_guard = H::mkIdent("second_guard", H::Sort::boolean());
    const auto first = builder.remember({guard, H::mkInt(7)});
    const auto second = builder.remember({second_guard, H::mkInt(8)});

    // An explicit true domain cannot remove a partial input's condition.
    const auto copied = builder.attach(H::mkInt(7), {first}, H::mkBool(true));
    VERIFY(builder.inspect(copied).defined == guard);
    // Reattaching the same pointer reads its existing guard before replacing it.
    VERIFY(builder.attach(first, {first}, H::mkBool(true)) == first);
    VERIFY(builder.inspect(first).defined == guard);

    const auto joint = builder.attach(H::mkInt(15), {first, second});
    const auto joint_guard = builder.inspect(joint).defined;
    VERIFY(joint_guard->kind == H::ExprKind::OP);
    VERIFY(joint_guard->op == H::Op::AND);
    VERIFY(joint_guard->args.size() == 2);
    VERIFY(joint_guard->args[0] == guard && joint_guard->args[1] == second_guard);

    const auto impossible = builder.attach(H::mkInt(1), {H::mkInt(2)}, H::mkBool(false));
    const auto impossible_guard = builder.inspect(impossible).defined;
    VERIFY(impossible_guard->kind == H::ExprKind::LIT_BOOL && !impossible_guard->bool_value);
    const auto propagated = builder.attach(H::mkInt(3), {impossible});
    VERIFY(!builder.inspect(propagated).defined->bool_value);

    // attach replaces the old guard when the new occurrence is total. A
    // partial dependent already attached above keeps its own original guard.
    VERIFY(builder.attach(first, {H::mkInt(0)}, H::mkBool(true)) == first);
    VERIFY(isTotal(builder, first));
    VERIFY(builder.inspect(copied).defined == guard);
    VERIFY(builder.attach(second, {}) == second);
    VERIFY(isTotal(builder, second));
    VERIFY(isTotal(builder, builder.attach(H::mkInt(9), {nullptr})));
    VERIFY(builder.attach(nullptr, {impossible}, H::mkBool(false)) == nullptr);

    // Total temporary occurrences must not stay owned by the guard registry.
    std::weak_ptr<const H::Expr> temporary;
    {
        auto value = builder.remember({guard, H::mkInt(11)});
        temporary = value;
        value = builder.attach(value, {}, H::mkBool(true));
        VERIFY(isTotal(builder, value));
    }
    VERIFY(temporary.expired());
    return 0;
}
