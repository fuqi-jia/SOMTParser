#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <memory>
#include <string>

namespace H = SOMTParser::Uir::Hir;

static std::shared_ptr<const H::Sort> setChain(std::size_t depth, H::Sort leaf) {
    auto root = std::make_shared<const H::Sort>(std::move(leaf));
    for (std::size_t i = 0; i < depth; ++i) {
        H::Sort parent;
        parent.kind = H::SortKind::SET;
        parent.elem = std::move(root);
        root = std::make_shared<const H::Sort>(std::move(parent));
    }
    return root;
}

static void checkRenaming() {
    {
        // The same DAG node has three lexical meanings. A cache keyed only by
        // node address incorrectly reuses a free rename below either binder.
        const auto x = H::mkIdent("x", H::Sort::boolean());
        const auto y = H::mkIdent("y", H::Sort::boolean());
        const auto body = H::mkApply("x", H::Sort::boolean(), {x, y});
        const auto bound_x = H::mkForall({{"x", H::Sort::boolean()}}, body);
        const auto bound_y = H::mkExists({{"y", H::Sort::boolean()}}, body);
        const auto source = H::mkOp(H::Op::AND, {body, bound_x, bound_y, body});
        const auto result = H::substituteIdents(source, {{"x", "xx"}, {"y", "yy"}});
        VERIFY(result->args[0] == result->args[3]);
        VERIFY(result->args[0]->name == "x"); // Function symbols are not identifiers.
        VERIFY(result->args[0]->args[0]->name == "xx");
        VERIFY(result->args[0]->args[1]->name == "yy");
        VERIFY(result->args[1]->args[0]->args[0] == x);
        VERIFY(result->args[1]->args[0]->args[1]->name == "yy");
        VERIFY(result->args[2]->args[0]->args[0]->name == "xx");
        VERIFY(result->args[2]->args[0]->args[1] == y);
        VERIFY(body->args[0] == x && body->args[1] == y);
    }
    {
        constexpr std::size_t depth = 200000;
        H::ExprPtr source = H::mkIdent("x", H::Sort::boolean(), {"deep", 7, 9});
        for (std::size_t i = 0; i < depth; ++i) {
            source = i % 127 == 0 ? H::mkOp(H::Op::AND, {source, source})
                                  : H::mkOp(H::Op::NOT, {source});
        }
        const auto result = H::substituteIdents(source, {{"x", "y"}});
        auto before = source;
        auto after = result;
        for (std::size_t i = 0; i < depth; ++i) {
            VERIFY(before != after);
            VERIFY(before->op == after->op);
            VERIFY(before->args.size() == after->args.size());
            if (after->args.size() == 2) VERIFY(after->args[0] == after->args[1]);
            before = before->args[0];
            after = after->args[0];
        }
        VERIFY(before->name == "x" && after->name == "y");
        VERIFY(after->loc.file == "deep" && after->loc.line == 7 && after->loc.column == 9);
        VERIFY(H::substituteIdents(source, {{"absent", "other"}}) == source);
    }
    {
        H::ExprPtr root = H::mkOp(H::Op::EQ, {H::mkIdent("x", H::Sort::integer()), H::mkInt(0)});
        for (std::size_t i = 0; i < 20000; ++i)
            root = H::mkForall({{"unused", H::Sort::integer()}}, root);
        auto renamed = H::substituteIdents(root, {{"x", "y"}}, {{"x", H::Sort::real()}});
        for (std::size_t i = 0; i < 20000; ++i) renamed = renamed->args[0];
        renamed = renamed->args[0];
        VERIFY(renamed->name == "y" && renamed->sort.kind == H::SortKind::REAL);
        const auto shadowed = H::mkExists({{"x", H::Sort::integer()}}, root);
        VERIFY(H::substituteIdents(shadowed, {{"x", "y"}}) == shadowed);
    }
}

static void checkSortOperations() {
    {
        constexpr std::size_t depth = 200000;
        const auto left = setChain(depth, H::Sort::boolean());
        const auto right = setChain(depth, H::Sort::boolean());
        const auto different = setChain(depth, H::Sort::integer());
        VERIFY(H::sameSort(*left, *right));
        VERIFY(!H::sameSort(*left, *different));
        const auto printed = H::toString(*left);
        VERIFY(printed.size() == depth * 6 + 4);
        VERIFY(printed.substr(0, 10) == "(Set (Set ");
        VERIFY(printed.substr(depth * 5, 4) == "Bool");
        VERIFY(printed.find_first_not_of(')', depth * 5 + 4) == std::string::npos);

        H::ConstraintModel model;
        model.decls.push_back({"deep_sort", *left});
        const auto requirements = model.setSolverRequirements();
        VERIFY(requirements.has_sets);
        VERIFY(requirements.infinite_or_unknown_carrier);
        VERIFY(requirements.non_integer_carrier); // Existing classification budget.
    }
    {
        // Shared diamonds must not turn equality into an exponential walk.
        auto left = std::make_shared<const H::Sort>(H::Sort::bitvec(8));
        auto right = std::make_shared<const H::Sort>(H::Sort::bitvec(8));
        for (std::size_t i = 0; i < 10000; ++i) {
            H::Sort a, b;
            a.kind = b.kind = H::SortKind::TUPLE;
            a.args = {left, left};
            b.args = {right, right};
            left = std::make_shared<const H::Sort>(a);
            right = std::make_shared<const H::Sort>(b);
        }
        VERIFY(H::sameSort(*left, *right));
    }
    {
        const auto complex = H::Sort::array(H::Sort::bitvec(3), H::Sort::tuple({
            H::Sort::set(H::Sort::boolean()), H::Sort::datatype("D", {H::Sort::real()}),
            H::Sort::sortApp("S", {H::Sort::floating(8, 24)}), H::Sort::tuple({})}));
        VERIFY(H::toString(complex) ==
               "(Array (_ BitVec 3) (Tuple (Set Bool) (D Real) (S (_ FloatingPoint 8 24)) UnitTuple))");
        VERIFY(!H::sameSort(H::Sort::tuple({H::Sort::boolean(), H::Sort::integer()}),
                            H::Sort::tuple({H::Sort::integer(), H::Sort::boolean()})));
        H::Sort malformed;
        malformed.kind = H::SortKind::ARRAY;
        VERIFY(!H::sameSort(malformed, malformed));
        VERIFY(H::toString(malformed) == "<malformed Array>");
        malformed.kind = H::SortKind::SET;
        VERIFY(!H::sameSort(malformed, malformed));
        VERIFY(H::toString(malformed) == "<malformed Set>");
        malformed.kind = H::SortKind::DATATYPE;
        malformed.name = "D";
        malformed.args = {nullptr};
        VERIFY(!H::sameSort(malformed, malformed));
        VERIFY(H::toString(malformed) == "(D <null>)");
        malformed.kind = H::SortKind::UNINTERPRETED;
        VERIFY(H::toString(malformed) == "(D <malformed>)");
    }
}

static void checkSetClassification() {
    for (const auto& carrier : {H::Sort::boolean(), H::Sort::bitvec(7),
                               H::Sort::floating(8, 24), H::Sort::roundingMode(),
                               H::Sort::tuple({}), H::Sort::set(H::Sort::boolean())}) {
        H::ConstraintModel model;
        model.decls.push_back({"finite", H::Sort::set(carrier)});
        const auto requirements = model.setSolverRequirements();
        VERIFY(requirements.has_sets && requirements.non_integer_carrier);
        VERIFY(!requirements.infinite_or_unknown_carrier);
    }
    H::DatatypeDecl box;
    box.name = "Box";
    box.params = {"T"};
    box.constructors = {{"box", {{"value", H::Sort::uninterpreted("T")}}}};
    for (bool finite : {false, true}) {
        H::ConstraintModel model;
        model.datatypes = {box};
        const auto instance = H::Sort::datatype("Box", {
            finite ? H::Sort::tuple({H::Sort::bitvec(4), H::Sort::roundingMode()})
                   : H::Sort::integer()});
        model.decls.push_back({"s", H::Sort::set(instance)});
        model.decls.push_back({"same", H::Sort::set(instance)}); // Cached instance.
        const auto result = model.setSolverRequirements();
        VERIFY(result.has_sets && result.non_integer_carrier);
        VERIFY(result.infinite_or_unknown_carrier == !finite);
    }
    {
        // Generic declarations alone require Set support, but do not claim a
        // concrete carrier. A concrete instance substitutes the lexical T.
        H::DatatypeDecl bag = box;
        bag.name = "Bag";
        bag.constructors[0].selectors[0].sort = H::Sort::set(H::Sort::uninterpreted("T"));
        H::ConstraintModel generic;
        generic.datatypes = {bag};
        const auto uninstantiated = generic.setSolverRequirements();
        VERIFY(uninstantiated.has_sets);
        VERIFY(!uninstantiated.non_integer_carrier && !uninstantiated.infinite_or_unknown_carrier);
        for (bool finite : {false, true}) {
            auto model = generic;
            model.decls.push_back({"bag", H::Sort::datatype("Bag", {
                finite ? H::Sort::boolean() : H::Sort::integer()})});
            const auto result = model.setSolverRequirements();
            VERIFY(result.has_sets);
            VERIFY(result.non_integer_carrier == finite);
            VERIFY(result.infinite_or_unknown_carrier == !finite);
        }
    }
    {
        // Recursive instance closure is unknown, not a finite enum. Conversely
        // a finite nullary datatype and a finite array carrier remain finite.
        H::DatatypeDecl list = box;
        list.name = "List";
        list.constructors.push_back({"cons", {{"tail", H::Sort::datatype("List", {
            H::Sort::uninterpreted("T")})}}});
        H::ConstraintModel recursive;
        recursive.datatypes = {list};
        recursive.decls.push_back({"s", H::Sort::set(H::Sort::datatype("List", {H::Sort::boolean()}))});
        VERIFY(recursive.setSolverRequirements().infinite_or_unknown_carrier);
        H::ConstraintModel finite;
        H::DatatypeDecl colour;
        colour.name = "Colour";
        colour.constructors = {{"red", {}}, {"green", {}}};
        finite.datatypes = {colour};
        finite.decls.push_back({"s", H::Sort::set(H::Sort::array(
            H::Sort::boolean(), H::Sort::datatype("Colour")))});
        VERIFY(!finite.setSolverRequirements().infinite_or_unknown_carrier);
        finite.datatypes[0].coinductive = true;
        VERIFY(finite.setSolverRequirements().infinite_or_unknown_carrier);
    }
    {
        H::ConstraintModel model;
        for (std::size_t i = 0; i < 100; ++i) {
            H::DatatypeDecl datatype;
            datatype.name = "D" + std::to_string(i);
            datatype.constructors = {{"c" + std::to_string(i), {{"f" + std::to_string(i),
                i == 99 ? H::Sort::boolean() : H::Sort::datatype("D" + std::to_string(i + 1))}}}};
            model.datatypes.push_back(std::move(datatype));
        }
        model.decls.push_back({"s", H::Sort::set(H::Sort::datatype("D0"))});
        VERIFY(!model.setSolverRequirements().infinite_or_unknown_carrier);
        model.datatypes.back().constructors[0].selectors[0].sort = H::Sort::integer();
        VERIFY(model.setSolverRequirements().infinite_or_unknown_carrier);
    }
}

int main() {
    checkRenaming();
    checkSortOperations();
    checkSetClassification();
    return 0;
}
