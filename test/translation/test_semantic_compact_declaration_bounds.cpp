#include "somtparser/translation/semantics.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <memory>

namespace H = SOMTParser::Uir::Hir;
namespace S = SOMTParser::Uir::Sem;
using SOMTParser::Uir::Diagnostics;
using SOMTParser::Uir::SourceLoc;

int main() {
    const SourceLoc loc{"bounds.mps", 19, 7};
    H::ConstraintModel model;
    model.decls.push_back({"integer", H::Sort::integer(), H::mkInt(-2), H::mkInt(3), loc});
    model.decls.push_back({"real", H::Sort::real(), H::mkReal("1/3"), H::mkInt(9), loc});
    model.decls.push_back({"upper", H::Sort::real(), {}, H::mkReal("4.5"), loc});
    model.decls.push_back({"auxiliary", H::Sort::integer(), H::mkInt(0), {}, loc});
    model.decls.back().auxiliary = true;
    model.decls.push_back({"free", H::Sort::integer(), {}, {}, loc});
    // Nonliteral bounds retain the general formula path, even when constant.
    const auto expression = H::mkOp(H::Op::ADD, {H::mkInt(2), H::mkInt(3)});
    model.decls.push_back({"expression", H::Sort::integer(), {}, expression, loc});
    auto ordinary = S::directLanguageToRelationalContract(
        model, "mps", SOMTParser::Uir::Fidelity::exact());
    VERIFY(ordinary.target_axioms.size() == 5);
    VERIFY(ordinary.target_declaration_bounds.empty());
    model.packed_linear_rows = std::make_shared<H::PackedLinearRows>();
    auto compact = S::directLanguageToRelationalContract(
        model, "mps", SOMTParser::Uir::Fidelity::exact());
    VERIFY(compact.target_axioms.size() == 1);
    VERIFY(compact.target_declaration_bounds.size() == 4);
    VERIFY(compact.target_axioms[0]->args[1] == expression);
    VERIFY(compact.target_signature.symbols.size() == 6);
    VERIFY(compact.source_signature.symbols.size() == 5);
    Diagnostics good;
    VERIFY(compact.validate(good));
    for (std::size_t i = 0; i < 4; ++i) {
        const auto& axiom = compact.target_declaration_bounds[i];
        VERIFY(axiom.target_symbol_index == i);
        VERIFY(axiom.lower_bound == model.decls[i].lower_bound);
        VERIFY(axiom.upper_bound == model.decls[i].upper_bound);
        const auto materialized = axiom.materialize(compact.target_signature);
        const auto expected = ordinary.target_axioms[i];
        VERIFY(materialized && materialized->kind == expected->kind);
        VERIFY(materialized->op == expected->op);
        VERIFY(materialized->args.size() == expected->args.size());
        VERIFY(materialized->loc.file == loc.file && materialized->loc.line == loc.line);
        for (std::size_t j = 0; j < expected->args.size(); ++j) {
            const auto& actual_term = materialized->args[j];
            const auto& expected_term = expected->args[j];
            if (expected_term->kind == H::ExprKind::IDENT) {
                VERIFY(actual_term->kind == H::ExprKind::IDENT);
                VERIFY(actual_term->name == expected_term->name);
                VERIFY(H::sameSort(actual_term->sort, expected_term->sort));
            } else {
                VERIFY(actual_term == expected_term);
            }
        }
    }
    // Post-pass bounds must come from the current model, including changes to
    // an auxiliary that is absent from the source-visible signature.
    model.decls[3].lower_bound = H::mkInt(-7);
    const auto target = S::relationalToSmtContract(
        model, false, compact.projection, compact.target_axioms,
        &compact.target_signature);
    VERIFY(target.target_declaration_bounds.size() == 4);
    VERIFY(target.target_declaration_bounds[3].lower_bound == model.decls[3].lower_bound);
    VERIFY(compact.target_declaration_bounds[3].lower_bound != model.decls[3].lower_bound);

    for (int mutation = 0; mutation < 5; ++mutation) {
        auto broken = compact;
        auto& axiom = broken.target_declaration_bounds.front();
        if (mutation == 0) { axiom.target_symbol_index = broken.target_signature.symbols.size(); }
        if (mutation == 1) { axiom.lower_bound = H::mkBool(true); }
        if (mutation == 2) {
            auto malformed = std::make_shared<H::Expr>(*H::mkReal("0.5"));
            malformed->sort = H::Sort::integer(); // Literal tag and sort disagree.
            axiom.lower_bound = malformed;
        }
        if (mutation == 3) { axiom.lower_bound.reset(); axiom.upper_bound.reset(); }
        if (mutation == 4) { axiom.target_symbol_index = 3; } // Same sort, wrong identity.
        Diagnostics bad;
        VERIFY(!broken.validate(bad));
        VERIFY(!axiom.materialize(broken.target_signature));
        VERIFY(bad.hasErrors());
    }
    {
        auto broken = compact;
        broken.target_declaration_bounds.push_back(broken.target_declaration_bounds.front());
        Diagnostics bad;
        VERIFY(!broken.validate(bad));
    }
    // MPS num() uses Real literals for explicit BV/LI/UI/LO/UP records,
    // including endpoints on Int columns. Check both that common case and
    // fractional endpoints, whose exact comparisons must not be rounded.
    {
        H::ConstraintModel mixed;
        mixed.decls.push_back({"binary", H::Sort::integer(), H::mkReal("0"), H::mkReal("1"), loc});
        mixed.decls.push_back({"fractional", H::Sort::integer(), H::mkReal("-1.5"), H::mkReal("2.25"), loc});
        mixed.decls.push_back({"rational", H::Sort::integer(), H::mkReal("1/3"), H::mkInt(2), loc});
        Diagnostics source_types;
        VERIFY(H::typeCheck(mixed, source_types));
        const auto expanded = S::directLanguageToRelationalContract(
            mixed, "mps", SOMTParser::Uir::Fidelity::exact());
        mixed.packed_linear_rows = model.packed_linear_rows;
        const auto reduced = S::directLanguageToRelationalContract(
            mixed, "mps", SOMTParser::Uir::Fidelity::exact());
        VERIFY(reduced.target_axioms.empty());
        VERIFY(reduced.target_declaration_bounds.size() == mixed.decls.size());
        Diagnostics valid;
        VERIFY(reduced.validate(valid));
        H::ConstraintModel reconstructed;
        for (std::size_t i = 0; i < mixed.decls.size(); ++i) {
            auto declaration = mixed.decls[i];
            declaration.lower_bound.reset();
            declaration.upper_bound.reset();
            reconstructed.decls.push_back(declaration);
            const auto formula = reduced.target_declaration_bounds[i].materialize(reduced.target_signature);
            const auto& expected = expanded.target_axioms[i];
            VERIFY(formula && formula->op == expected->op);
            VERIFY(formula->args.size() == 3);
            VERIFY(formula->args[0] == expected->args[0]);
            VERIFY(formula->args[2] == expected->args[2]);
            VERIFY(formula->args[1]->name == declaration.name);
            VERIFY(formula->args[1]->sort.kind == H::SortKind::INT);
            H::Constraint constraint;
            constraint.formula = formula;
            reconstructed.constraints.push_back(constraint);
        }
        Diagnostics reconstructed_types;
        VERIFY(H::typeCheck(reconstructed, reconstructed_types));
    }
    {
        auto extended_model = model;
        S::TranslationPipeline pipeline;
        pipeline.add(S::directLanguageToRelationalContract(
            extended_model, "mps", SOMTParser::Uir::Fidelity::exact()));
        H::FunDecl helper;
        helper.name = "helper";
        helper.result = H::Sort::integer();
        helper.body = H::mkOp(H::Op::ADD,
            {H::mkIdent("integer", H::Sort::integer()), H::mkInt(1)});
        helper.auxiliary = true;
        extended_model.funs.push_back(helper);
        Diagnostics good_extension;
        VERIFY(S::extendRelationalWithDefinedHelpers(
            extended_model, "test-helper", pipeline, good_extension));
        VERIFY(pipeline.stages().size() == 2);
        const auto& before = pipeline.stages().front();
        const auto& after = pipeline.stages().back();
        VERIFY(after.target_declaration_bounds.size() == before.target_declaration_bounds.size());
        for (std::size_t i = 0; i < before.target_declaration_bounds.size(); ++i) {
            const auto& left = before.target_declaration_bounds[i];
            const auto& right = after.target_declaration_bounds[i];
            VERIFY(left.target_symbol_index == right.target_symbol_index);
            VERIFY(left.target_name == right.target_name);
            VERIFY(left.lower_bound == right.lower_bound && left.upper_bound == right.upper_bound);
            VERIFY(right.materialize(after.target_signature));
        }
        VERIFY(pipeline.validate(good_extension));
    }
    // Each lower/upper pair remains represented once; consumers can inspect
    // endpoint identity without materializing the full family of formulas.
    H::ConstraintModel wide;
    wide.packed_linear_rows = model.packed_linear_rows;
    const auto zero = H::mkReal("0");
    const auto one = H::mkReal("1");
    for (std::size_t i = 0; i < 2048; ++i) {
        wide.decls.push_back({"column" + std::to_string(i), H::Sort::integer(), zero, one, loc});
    }
    const auto many = S::directLanguageToRelationalContract(
        wide, "mps", SOMTParser::Uir::Fidelity::exact());
    VERIFY(many.target_axioms.empty());
    VERIFY(many.target_declaration_bounds.size() == wide.decls.size());
    for (std::size_t i = 0; i < wide.decls.size(); ++i) {
        VERIFY(many.target_declaration_bounds[i].target_symbol_index == i);
        VERIFY(many.target_declaration_bounds[i].lower_bound == zero);
        VERIFY(many.target_declaration_bounds[i].upper_bound == one);
    }
    return 0;
}
