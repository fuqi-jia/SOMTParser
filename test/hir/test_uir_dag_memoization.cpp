#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/hir.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <iostream>
#include <string>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;
namespace L = SOMTParser::Lower;

static H::ExprPtr doubledBoolDag(unsigned levels) {
    H::ExprPtr expression = H::mkBool(true);
    for (unsigned i = 0; i < levels; ++i) {
        // The two operands deliberately point to the same immutable child.
        expression = H::mkOp(H::Op::AND, {expression, expression});
    }
    return expression;
}

int main() {
    std::cout << "======= HIR shared-DAG checking and lowering =======\n";

    // A depth-40 binary DAG has only 41 distinct nodes. Tree-recursive
    // visitors would visit over a trillion leaves.
    H::ConstraintModel dag_model;
    H::Constraint dag_constraint;
    dag_constraint.formula = doubledBoolDag(40);
    dag_model.constraints.push_back(dag_constraint);
    U::Diagnostics dag_check_diagnostics;
    VERIFY(H::typeCheck(dag_model, dag_check_diagnostics));
    VERIFY(!dag_check_diagnostics.hasErrors());
    auto parser = SOMTParser::newParser();
    L::HirToParser lowering(parser);
    U::TranslationReport report;
    U::Diagnostics lowering_diagnostics;
    VERIFY(lowering.lower(dag_model, report, lowering_diagnostics));
    VERIFY(!lowering_diagnostics.hasErrors());

    // A cache indexed only by Expr* would accept this: the first use checks
    // the shared BOUND_VAR under Bool, and the second use must fail under Int.
    H::ExprPtr shared_bound = H::mkBoundVar("x", H::Sort::boolean());
    H::ExprPtr bool_scope = H::mkForall({{"x", H::Sort::boolean()}}, shared_bound);
    H::ExprPtr int_scope = H::mkForall({{"x", H::Sort::integer()}}, shared_bound);
    H::ConstraintModel scope_model;
    H::Constraint scope_constraint;
    scope_constraint.formula = H::mkOp(H::Op::AND, {bool_scope, int_scope});
    scope_model.constraints.push_back(scope_constraint);
    U::Diagnostics scope_diagnostics;
    VERIFY(!H::typeCheck(scope_model, scope_diagnostics));
    VERIFY(scope_diagnostics.hasErrors());
    bool saw_sort_mismatch = false;
    for (const auto& diagnostic : scope_diagnostics.all()) {
        saw_sort_mismatch = saw_sort_mismatch
            || diagnostic.message.find("bound variable 'x' is used as Bool")
                   != std::string::npos;
    }
    VERIFY(saw_sort_mismatch);

    // The same bound node in separate function roots must lower against each
    // function's fresh parameter, rather than retaining the previous root's
    // parameter node from the cache.
    H::ExprPtr shared_parameter = H::mkBoundVar("p", H::Sort::boolean());
    H::ConstraintModel functions;
    H::FunDecl f;
    f.name = "f";
    f.params = {H::Sort::boolean()};
    f.result = H::Sort::boolean();
    f.binders = {{"p", H::Sort::boolean()}};
    f.body = shared_parameter;
    functions.funs.push_back(f);
    H::FunDecl g = f;
    g.name = "g";
    g.body = shared_parameter;
    functions.funs.push_back(g);
    auto function_parser = SOMTParser::newParser();
    L::HirToParser function_lowering(function_parser);
    U::TranslationReport function_report;
    U::Diagnostics function_diagnostics;
    VERIFY(function_lowering.lower(functions, function_report,
                                   function_diagnostics));
    const std::string smt = function_parser->dumpSMT2();
    VERIFY(smt.find("(define-fun f ((__somt_hir_param_0 Bool)) Bool __somt_hir_param_0)")
           != std::string::npos);
    VERIFY(smt.find("(define-fun g ((__somt_hir_param_1 Bool)) Bool __somt_hir_param_1)")
           != std::string::npos);
    VERIFY(!function_diagnostics.hasErrors());
    return 0;
}
