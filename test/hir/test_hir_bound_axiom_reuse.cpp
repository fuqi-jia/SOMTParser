#include "somtparser/translation/semantics.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;
namespace S = SOMTParser::Uir::Sem;

int main() {
    H::ConstraintModel model;
    const SourceLoc source{"bounded-source.xml", 17, 3};
    model.decls.push_back({"x", H::Sort::integer(), H::mkInt(-2), H::mkInt(3), source});
    model.decls.push_back({"lower", H::Sort::real(), H::mkReal("1.5"), {}, source});
    model.decls.push_back({"upper", H::Sort::integer(), {}, H::mkInt(8), source});
    model.decls.push_back({"unbounded", H::Sort::integer(), {}, {}, source});
    // A target-stage contract normally reconstructs the same bounded-variable
    // axioms already present in the source stage. Exact immutable matches can
    // be shared; altered hints must retain the ordinary fresh-construction path.
    const auto source_contract = S::miniZincToRelationalContract(model);
    const auto target_reused = S::relationalToSmtContract(
        model, true, source_contract.projection, source_contract.target_axioms);
    VERIFY(target_reused.target_axioms.size() == source_contract.target_axioms.size());
    for (std::size_t i = 0; i < target_reused.target_axioms.size(); ++i) {
        VERIFY(target_reused.target_axioms[i] == source_contract.target_axioms[i]);
    }
    const auto target_empty_projection = S::relationalToSmtContract(
        model, true, S::ModelProjection{}, source_contract.target_axioms);
    const auto target_default = S::relationalToSmtContract(model, true);
    VERIFY(target_empty_projection.target_axioms.size() == target_default.target_axioms.size());
    VERIFY(target_empty_projection.projection.observables.size()
           == target_default.projection.observables.size());

    const auto interval_hint = source_contract.target_axioms[0];
    const auto bad_location = H::mkOp(
        H::Op::LE, interval_hint->args, SourceLoc{"different.xml", source.line, source.column});
    const auto bad_bound = H::mkOp(
        H::Op::LE, {interval_hint->args[0], interval_hint->args[1], H::mkInt(4)}, source);
    const auto bad_arity = H::mkOp(
        H::Op::LE, {interval_hint->args[0], interval_hint->args[1]}, source);
    const auto bad_relation = H::mkOp(
        H::Op::LT, interval_hint->args, source);
    const auto bad_name = H::mkOp(
        H::Op::LE, {interval_hint->args[0], H::mkIdent("not_x", H::Sort::integer()),
                    interval_hint->args[2]}, source);
    const auto bad_sort = H::mkOp(
        H::Op::LE, {interval_hint->args[0], H::mkIdent("x", H::Sort::real()),
                    interval_hint->args[2]}, source);
    for (const auto& invalid_hint : {bad_location, bad_bound, bad_arity, bad_relation,
                                     bad_name, bad_sort}) {
        const auto fallback = S::relationalToSmtContract(
            model, true, source_contract.projection, {invalid_hint});
        VERIFY(fallback.target_axioms.size() == source_contract.target_axioms.size());
        VERIFY(fallback.target_axioms[0] != invalid_hint);
        VERIFY(fallback.target_axioms[0]->args[0] == model.decls[0].lower_bound);
        VERIFY(fallback.target_axioms[0]->args[2] == model.decls[0].upper_bound);
        VERIFY(fallback.target_axioms[0]->loc.file == source.file);
    }

    // A post-pass change to even one bound pointer invalidates the candidate
    // axiom and preserves all current declaration bounds in the rebuilt one.
    H::ConstraintModel changed = model;
    changed.decls[0].upper_bound = H::mkInt(9);
    const auto fallback_after_rewrite = S::relationalToSmtContract(
        changed, true, source_contract.projection, source_contract.target_axioms);
    VERIFY(fallback_after_rewrite.target_axioms[0] != source_contract.target_axioms[0]);
    VERIFY(fallback_after_rewrite.target_axioms[0]->args[2] == changed.decls[0].upper_bound);
    return 0;
}
