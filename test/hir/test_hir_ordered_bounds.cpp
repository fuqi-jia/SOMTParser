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
    const auto contract = S::miniZincToRelationalContract(model);
    VERIFY(contract.target_axioms.size() == 3);
    const auto interval = contract.target_axioms[0];
    VERIFY(interval->op == H::Op::LE);
    VERIFY(interval->args.size() == 3);
    VERIFY(interval->args[0] == model.decls[0].lower_bound);
    VERIFY(interval->args[2] == model.decls[0].upper_bound);
    VERIFY(interval->args[1]->name == "x");
    VERIFY(interval->loc.file == source.file && interval->loc.line == source.line);
    VERIFY(contract.target_axioms[1]->op == H::Op::GE);
    VERIFY(contract.target_axioms[2]->op == H::Op::LE);
    for (const auto& axiom : contract.target_axioms) {
        H::Constraint constraint;
        constraint.formula = axiom;
        model.constraints.push_back(constraint);
    }
    Diagnostics diagnostics;
    VERIFY(H::typeCheck(model, diagnostics));
    VERIFY(contract.validate(diagnostics));
    const auto x = H::mkIdent("x", H::Sort::integer());
    std::vector<H::ExprPtr> hints{x, H::mkIdent("lower", H::Sort::real()),
                                 H::mkIdent("upper", H::Sort::integer())};
    const auto shared = S::xcsp3ToRelationalContract(model, Fidelity::exact(), hints);
    VERIFY(shared.target_axioms[0]->args[1] == x);
    VERIFY(shared.target_axioms[1]->args[0] == hints[1]);
    VERIFY(shared.target_axioms[2]->args[0] == hints[2]);
    VERIFY(shared.target_axioms[0]->loc.file == source.file);
    // Cache entries are only hints. A wrong name, wrong sort, or bound
    // variable cannot change which free source variable the axiom constrains.
    for (const auto& bad : {H::mkIdent("other", H::Sort::integer()),
                           H::mkIdent("x", H::Sort::real()),
                           H::mkBoundVar("x", H::Sort::integer()), H::ExprPtr{}}) {
        const auto fallback = S::xcsp3ToRelationalContract(model, Fidelity::exact(), {bad});
        const auto variable = fallback.target_axioms[0]->args[1];
        VERIFY(variable && variable->kind == H::ExprKind::IDENT);
        VERIFY(variable->name == "x" && H::sameSort(variable->sort, H::Sort::integer()));
        VERIFY(variable != bad);
    }
    for (auto op : {H::Op::LE, H::Op::LT, H::Op::GE, H::Op::GT}) {
        H::ConstraintModel ordered;
        H::Constraint constraint;
        constraint.formula = H::mkOp(op, {H::mkInt(-2), H::mkReal("1.5"), H::mkInt(3)});
        ordered.constraints.push_back(constraint);
        Diagnostics good;
        VERIFY(H::typeCheck(ordered, good));
        ordered.constraints[0].formula = H::mkOp(op, {H::mkInt(1)});
        Diagnostics arity;
        VERIFY(!H::typeCheck(ordered, arity));
        ordered.constraints[0].formula = H::mkOp(op, {H::mkInt(1), H::mkBool(true), H::mkInt(2)});
        Diagnostics sort;
        VERIFY(!H::typeCheck(ordered, sort));
    }
    return 0;
}
