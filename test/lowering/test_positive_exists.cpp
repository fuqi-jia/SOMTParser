#include "somtparser/lowering/positive_exists.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/translation/translate.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <set>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;
namespace L = SOMTParser::Lower;

static H::ExprPtr integer(const std::string& name) {
    return H::mkBoundVar(name, H::Sort::integer());
}
static H::ExprPtr exists(const std::string& name, H::ExprPtr body) {
    return H::mkExists({{name, H::Sort::integer()}}, std::move(body));
}
static H::ExprPtr equal(H::ExprPtr a, H::ExprPtr b) {
    return H::mkOp(H::Op::EQ, {std::move(a), std::move(b)});
}
static void valid(const H::ConstraintModel& model) {
    U::Diagnostics diags;
    VERIFY(H::typeCheck(model, diags));
    VERIFY(!diags.hasErrors());
}

int main() {
    {
        H::ConstraintModel model;
        auto root = H::mkBool(true);
        for (unsigned i = 0; i < 100; ++i) { root = H::mkOp(H::Op::AND, {root, root}); }
        model.constraints.push_back({root});
        VERIFY(L::liftPositiveExists(model).empty());
        VERIFY(model.constraints[0].formula == root && model.decls.empty());
        auto witness = exists("rank", equal(integer("rank"), H::mkInt(1)));
        model.constraints[0].formula = H::mkOp(H::Op::AND, {witness, root});
        VERIFY(L::liftPositiveExists(model).size() == 1);
        VERIFY(model.constraints[0].formula->args[1] == root);
    }
    {
        H::ConstraintModel model;
        model.decls.push_back({"g", H::Sort::integer()});
        const auto x = H::mkIdent("g", H::Sort::integer());
        auto e = exists("x", equal(integer("x"), x));
        auto nested = exists("x", H::mkOp(H::Op::AND, {
            equal(integer("x"), H::mkInt(3)),
            exists("z", equal(integer("z"), H::mkInt(7)))}));
        auto negative = H::mkOp(H::Op::NOT, {e});
        auto reified = equal(e, H::mkBool(false));
        auto disjunction = H::mkOp(H::Op::OR, {e, H::mkBool(false)});
        auto implication = H::mkOp(H::Op::IMPLIES, {H::mkBool(true), e});
        auto universal = H::mkForall({{"z", H::Sort::integer()}}, e);
        model.constraints.push_back({H::mkOp(H::Op::AND,
            {e, e, nested, negative, reified, disjunction, implication, universal})});
        H::Constraint soft; soft.formula = e; soft.soft = true;
        model.constraints.push_back(soft);
        valid(model);
        const auto original = model.constraints[0].formula;
        const auto lifted = L::liftPositiveExists(model);
        VERIFY(lifted.size() == 4 && model.decls.size() == 5);
        std::set<std::string> names;
        for (const auto& witness : lifted) {
            VERIFY(names.insert(witness.symbol_name).second);
            VERIFY(witness.bound_name == "x" || witness.bound_name == "z");
            VERIFY(witness.constraint_index == 0);
        }
        for (std::size_t i = 1; i < model.decls.size(); ++i) { VERIFY(model.decls[i].auxiliary); }
        const auto& args = model.constraints[0].formula->args;
        VERIFY(args[0]->args[0]->kind == H::ExprKind::IDENT);
        VERIFY(args[0]->args[1] == x); // free global remains unchanged
        VERIFY(args[0]->args[0]->name != args[1]->args[0]->name);
        VERIFY(args[2]->args[0]->args[0]->name != args[2]->args[1]->args[0]->name);
        VERIFY(args[3] == negative && args[4] == reified && args[5] == disjunction);
        VERIFY(args[6] == implication && args[7] == universal);
        VERIFY(model.constraints[1].formula == e);
        VERIFY(original->args[0] == e && e->kind == H::ExprKind::EXISTS);
        valid(model);
        VERIFY(L::liftPositiveExists(model).empty());
    }
    {
        H::ConstraintModel model;
        model.decls.push_back({"|!somt_exists_0|", H::Sort::integer()});
        model.decls.push_back({"!somt_exists_1", H::Sort::integer()});
        model.funs.push_back({"!somt_exists_2", {}, H::Sort::integer()});
        auto e = H::mkExists({{"|!somt_exists_3|", H::Sort::integer()},
                              {"flag", H::Sort::boolean()}},
            H::mkOp(H::Op::AND, {
                equal(integer("|!somt_exists_3|"), H::mkInt(4)),
                H::mkBoundVar("flag", H::Sort::boolean())}));
        model.constraints.push_back({e});
        valid(model);
        const auto lifted = L::liftPositiveExists(model);
        VERIFY(lifted.size() == 2);
        VERIFY(lifted[0].symbol_name == "!somt_exists_4");
        VERIFY(lifted[1].symbol_name == "!somt_exists_5");
        valid(model);
    }
    {
        // An outer witness captured in a retained quantifier is replaced,
        // but that quantifier's own binder and inner exists stay scoped.
        H::ConstraintModel model;
        auto inner = H::mkForall({{"y", H::Sort::integer()}},
            exists("z", equal(integer("z"),
                H::mkOp(H::Op::ADD, {integer("x"), integer("y")}))));
        model.constraints.push_back({exists("x", inner)});
        valid(model);
        const auto lifted = L::liftPositiveExists(model);
        VERIFY(lifted.size() == 1);
        const auto output = model.constraints[0].formula;
        VERIFY(output->kind == H::ExprKind::FORALL);
        VERIFY(output->args[0]->kind == H::ExprKind::EXISTS);
        const auto rhs = output->args[0]->args[0]->args[1];
        VERIFY(rhs->args[0]->kind == H::ExprKind::IDENT);
        VERIFY(rhs->args[1]->kind == H::ExprKind::BOUND_VAR);
        valid(model);
    }
    {
        H::ConstraintModel model;
        model.decls.push_back({"x", H::Sort::integer(), H::mkInt(0), H::mkInt(9)});
        const auto x = H::mkIdent("x", H::Sort::integer());
        model.constraints.push_back({exists("rank", equal(x, integer("rank")))});
        H::Objective objective; objective.kind = H::ObjKind::MINIMIZE; objective.term = x;
        model.objectives.push_back(objective);
        SOMTParser::TranslateOptions options;
        options.omt_dialect = L::OmtDialect::Z3;
        const auto translated = SOMTParser::translate(model, options);
        VERIFY(translated.ok());
        const auto smt = translated.toSmt2();
        VERIFY(smt.find("(exists") == std::string::npos);
        VERIFY(smt.find("!somt_exists_0") != std::string::npos);
        VERIFY(smt.find("(minimize x)") != std::string::npos);
        VERIFY(model.decls.size() == 1);
        VERIFY(model.constraints[0].formula->kind == H::ExprKind::EXISTS);
        VERIFY(translated.report().fidelity().count_status == U::CountStatus::NO_GUARANTEE);
        U::Fidelity count_required;
        count_required.count_status = U::CountStatus::PRESERVED;
        VERIFY(!translated.report().fidelity().meets(count_required));
        const auto& stage = translated.semantics().stages().back();
        VERIFY(stage.source_signature.symbols.size() == 1);
        VERIFY(stage.target_signature.symbols.size() == 2);
        VERIFY(stage.projection.observables.size() == 1);
        VERIFY(stage.projection.observables[0].source_name == "x");
    }
    return 0;
}
