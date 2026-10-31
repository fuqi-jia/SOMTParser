// HIR expressions are immutable; the ConstraintModel container is not.
#include "somtparser/hir/hir.h"
#include <cassert>
#include <iostream>

using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

int main() {
    // Leaves.
    const ExprPtr t = mkBool(true);
    assert(t->kind == ExprKind::LIT_BOOL);
    assert(t->bool_value);
    assert(t->sort.kind == SortKind::BOOL);
    assert(t->args.empty());

    const ExprPtr three = mkInt(3);
    assert(three->kind == ExprKind::LIT_INT);
    assert(three->int_value == 3);
    assert(three->sort.kind == SortKind::INT);

    const ExprPtr x = mkIdent("x", Sort::integer());
    assert(x->kind == ExprKind::IDENT);
    assert(x->name == "x");
    assert(x->sort.kind == SortKind::INT);

    // (> (+ x 3) 0)
    const ExprPtr sum = mkOp(Op::ADD, {x, three});
    assert(sum->kind == ExprKind::OP);
    assert(sum->op == Op::ADD);
    assert(sum->args.size() == 2);
    assert(sum->args[0] == x);
    assert(sum->args[1] == three);
    assert(sum->sort.kind == SortKind::INT);

    const ExprPtr cmp = mkOp(Op::GT, {sum, mkInt(0)});
    assert(cmp->op == Op::GT);
    assert(cmp->args.size() == 2);
    assert(cmp->args[0] == sum);
    assert(cmp->args[1]->kind == ExprKind::LIT_INT);
    assert(cmp->args[1]->int_value == 0);
    assert(cmp->sort.kind == SortKind::BOOL);   // comparisons are Bool

    // A model carrying one int variable, one hard constraint, one objective.
    ConstraintModel m;
    VarDecl d;
    d.name = "x";
    d.sort = Sort::integer();
    d.lower_bound = mkInt(0);
    d.upper_bound = mkInt(10);
    m.decls.push_back(d);

    Constraint c;
    c.formula = cmp;
    m.constraints.push_back(c);

    Objective o;
    o.kind = ObjKind::MINIMIZE;
    o.term = x;
    o.name = "obj";
    m.objectives.push_back(o);

    // The feature profile is what the pass manager validates against and what
    // the report publishes as the domain fingerprint.
    const auto f = m.features();
    assert(f.count(feat::intVar()) == 1);
    assert(f.count(feat::softConstraint()) == 0);
    assert(f.count(feat::realVar()) == 0);

    // A soft constraint shows up as a feature.
    Constraint s;
    s.formula = mkBool(true);
    s.soft = true;
    s.weight = 2.5;
    s.group = "g1";
    m.constraints.push_back(s);
    const auto f2 = m.features();
    assert(f2.count(feat::softConstraint()) == 1);

    // Nonlinearity is detected structurally, since it drives theory choice.
    ConstraintModel n;
    VarDecl dy;
    dy.name = "y";
    dy.sort = Sort::integer();
    n.decls.push_back(dy);
    Constraint nc;
    nc.formula = mkOp(Op::EQ, {mkOp(Op::MUL, {mkIdent("y", Sort::integer()),
                                              mkIdent("y", Sort::integer())}),
                               mkInt(4)});
    n.constraints.push_back(nc);
    assert(n.features().count(feat::nonlinear()) == 1);

    // Multiplication by a constant stays linear.
    ConstraintModel l;
    VarDecl dz;
    dz.name = "z";
    dz.sort = Sort::integer();
    l.decls.push_back(dz);
    Constraint lc;
    lc.formula = mkOp(Op::EQ, {mkOp(Op::MUL, {mkInt(2), mkIdent("z", Sort::integer())}),
                               mkInt(4)});
    l.constraints.push_back(lc);
    assert(l.features().count(feat::nonlinear()) == 0);

    std::cout << "All HIR tests passed." << std::endl;
    return 0;
}
