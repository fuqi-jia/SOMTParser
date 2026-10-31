// Parameter substitution and nominal datatype validation recurse through
// every supported sort container before any sort reaches lowering.
#include "somtparser/hir/typecheck.h"

#include <iostream>

#include "test_helpers.h"

using namespace SOMTParser::Uir::Hir;
using SOMTParser::Uir::Diagnostics;

namespace H = SOMTParser::Uir::Hir;

namespace {

void constrain(ConstraintModel& model, ExprPtr formula) {
    Constraint item;
    item.formula = std::move(formula);
    model.constraints.push_back(std::move(item));
}

bool accepted(const ConstraintModel& model) {
    Diagnostics diagnostics;
    return typeCheck(model, diagnostics);
}

} // namespace

int main() {
    const Sort int_sort = Sort::integer();
    const Sort bool_sort = Sort::boolean();
    const Sort parameter = Sort::uninterpreted("T");
    const Sort wrapped_bool = Sort::datatype("Wrap", {bool_sort});
    const Sort array_bool = Sort::array(int_sort, bool_sort);
    const Sort bool_array_bool = Sort::array(bool_sort, bool_sort);
    const Sort set_bool = Sort::set(bool_sort);

    // `T` substitution must reach both Array components and Set.element. Test
    // the constructor arguments as well as selector result sorts so both
    // checker paths use the same recursive substitution.
    {
        DatatypeDecl wrap;
        wrap.name = "Wrap";
        wrap.params = {"T"};
        wrap.constructors.push_back({
            "wrap",
            {{"array_payload", Sort::array(int_sort, parameter)},
             {"index_payload", Sort::array(parameter, bool_sort)},
             {"set_payload", Sort::set(parameter)}}});

        ConstraintModel model;
        model.datatypes.push_back(wrap);
        model.decls.push_back({"w", wrapped_bool, nullptr, nullptr, {}});
        model.decls.push_back({"a", array_bool, nullptr, nullptr, {}});
        model.decls.push_back({"index_array", bool_array_bool, nullptr, nullptr, {}});
        model.decls.push_back({"s", set_bool, nullptr, nullptr, {}});
        constrain(model, mkOp(Op::EQ, {mkIdent("w", wrapped_bool),
                                       mkDtConstructor("wrap", wrapped_bool,
                                                       {mkIdent("a", array_bool),
                                                        mkIdent("index_array", bool_array_bool),
                                                        mkIdent("s", set_bool)})}));
        constrain(model, mkOp(Op::EQ, {
            mkDtSelector("array_payload", array_bool, mkIdent("w", wrapped_bool)),
            mkIdent("a", array_bool)}));
        constrain(model, mkOp(Op::EQ, {
            mkDtSelector("index_payload", bool_array_bool,
                         mkIdent("w", wrapped_bool)),
            mkIdent("index_array", bool_array_bool)}));
        constrain(model, mkOp(Op::EQ, {
            mkDtSelector("set_payload", set_bool, mkIdent("w", wrapped_bool)),
            mkIdent("s", set_bool)}));
        VERIFY(accepted(model));
    }

    // Nested unknown nominal names and wrong datatype arities must be rejected
    // by typeCheck, rather than surfacing later in HirToParser::lowerSort.
    {
        DatatypeDecl outer;
        outer.name = "Outer";
        outer.constructors.push_back({
            "outer", {{"payload", Sort::array(int_sort, Sort::datatype("Ghost"))}}});
        ConstraintModel model;
        model.datatypes.push_back(outer);
        VERIFY(!accepted(model));
    }
    {
        DatatypeDecl leaf;
        leaf.name = "Leaf";
        leaf.constructors.push_back({"leaf", {}});
        DatatypeDecl outer;
        outer.name = "Outer";
        outer.constructors.push_back({
            "outer", {{"payload", Sort::set(Sort::datatype("Leaf", {int_sort}))}}});
        ConstraintModel model;
        model.datatypes = {leaf, outer};
        VERIFY(!accepted(model));
    }
    {
        ConstraintModel model;
        model.decls.push_back({"bad", Sort::array(int_sort, Sort::datatype("Ghost")),
                               nullptr, nullptr, {}});
        VERIFY(!accepted(model));
    }

    std::cout << "Datatype sort closure checks passed.\n";
    return 0;
}
