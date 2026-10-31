// Exact non-recursive HIR functions remain shared SMT definitions, not axioms
// or eagerly expanded copies at every call site.
#include "somtparser/translation/translate.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/translation/semantics.h"
#include "test_helpers.h"

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

namespace H = SOMTParser::Uir::Hir;

namespace {

H::FunDecl defined(std::string name, std::string binder, H::ExprPtr body,
                   bool auxiliary = false) {
    H::FunDecl function;
    function.name = std::move(name);
    function.params = {H::Sort::integer()};
    function.result = H::Sort::integer();
    function.binders = {{std::move(binder), H::Sort::integer()}};
    function.body = std::move(body);
    function.auxiliary = auxiliary;
    return function;
}

bool accepted(const H::ConstraintModel& model) {
    SOMTParser::Uir::Diagnostics diagnostics;
    const bool result = H::typeCheck(model, diagnostics);
    VERIFY(result == !diagnostics.hasErrors());
    return result;
}

bool rejectsStaleIdentSort(const H::Sort& declared_sort,
                           const H::Sort& recorded_sort,
                           H::ConstraintModel model = {}) {
    H::VarDecl variable;
    variable.name = "value";
    variable.sort = declared_sort;
    model.decls.push_back(std::move(variable));
    H::FunDecl function;
    function.name = "read_value";
    function.result = recorded_sort;
    function.body = H::mkIdent("value", recorded_sort);
    model.funs.push_back(std::move(function));

    SOMTParser::Uir::Diagnostics diagnostics;
    const bool result = H::typeCheck(model, diagnostics);
    VERIFY(result == !diagnostics.hasErrors());
    bool found_identifier_sort_error = false;
    for (const auto& diagnostic : diagnostics.all()) {
        found_identifier_sort_error = found_identifier_sort_error
            || diagnostic.message.find("is used as ") != std::string::npos;
    }
    VERIFY(found_identifier_sort_error == !result);
    return !result;
}

H::ConstraintModel twoHelpers() {
    H::ConstraintModel model;
    H::VarDecl x;
    x.name = "x";
    x.sort = H::Sort::integer();
    model.decls.push_back(x);

    // Store caller before callee to ensure lowering topologically orders the
    // definitions instead of depending on vector insertion order.
    auto f_arg = H::mkBoundVar("y", H::Sort::integer());
    auto g_call = H::mkApply("g", H::Sort::integer(), {f_arg});
    model.funs.push_back(defined(
        "f", "y", H::mkOp(H::Op::MUL, {g_call, H::mkInt(2)}), true));
    model.funs.push_back(defined(
        "g", "z", H::mkOp(H::Op::ADD,
                           {H::mkBoundVar("z", H::Sort::integer()), H::mkInt(1)}),
        true));
    auto f_x = H::mkApply("f", H::Sort::integer(), {H::mkIdent("x", H::Sort::integer())});
    H::Constraint constraint;
    constraint.formula = H::mkOp(H::Op::EQ, {f_x, H::mkInt(4)});
    model.constraints.push_back(std::move(constraint));
    return model;
}

} // namespace

int main(int argc, char** argv) {
    H::ConstraintModel model = twoHelpers();
    VERIFY(accepted(model));

    auto translated = SOMTParser::translate(model);
    VERIFY(translated.ok());
    const std::string smt = translated.toSmt2();
    const auto g_definition = smt.find("(define-fun g ");
    const auto f_definition = smt.find("(define-fun f ");
    VERIFY(g_definition != std::string::npos);
    VERIFY(f_definition != std::string::npos);
    VERIFY(g_definition < f_definition);
    VERIFY(smt.find("(f x)") != std::string::npos);

    // The HIR-to-SMT contract starts at the relational-core boundary, where
    // helpers are real source functions. The preceding language adapter keeps
    // them target-only and omits them from end-user projections.
    bool internal_signature_has_helpers = false;
    for (const auto& stage : translated.semantics().stages()) {
        bool has_f = false;
        bool has_g = false;
        for (const auto& symbol : stage.source_signature.symbols) {
            has_f = has_f || symbol.name == "f";
            has_g = has_g || symbol.name == "g";
        }
        internal_signature_has_helpers = internal_signature_has_helpers || (has_f && has_g);
    }
    VERIFY(internal_signature_has_helpers);

    const auto frontend = SOMTParser::Uir::Sem::directLanguageToRelationalContract(
        model, "smtlib2", SOMTParser::Uir::Fidelity{});
    SOMTParser::Uir::Diagnostics frontend_diagnostics;
    const bool frontend_valid = frontend.validate(frontend_diagnostics);
    if (!frontend_valid) {
        for (const auto& diagnostic : frontend_diagnostics.all()) {
            std::cerr << diagnostic.message << '\n';
        }
    }
    VERIFY(frontend_valid);
    VERIFY(!frontend_diagnostics.hasErrors());
    bool frontend_target_has_helpers = false;
    for (const auto& symbol : frontend.target_signature.symbols) {
        frontend_target_has_helpers = frontend_target_has_helpers
                                      || symbol.name == "f" || symbol.name == "g";
    }
    VERIFY(frontend_target_has_helpers);
    for (const auto& symbol : frontend.source_signature.symbols) {
        VERIFY(symbol.name != "f" && symbol.name != "g");
    }
    for (const auto& observable : frontend.projection.observables) {
        VERIFY(observable.source_name != "f" && observable.source_name != "g");
        VERIFY(observable.target_name != "f" && observable.target_name != "g");
    }

    // A binder and a free identifier may have the same HIR spelling: BOUND_VAR
    // denotes the parameter while IDENT continues to denote the global. Lowering
    // must alpha-rename only the emitted parameter, leaving the global mapping
    // untouched.
    H::ConstraintModel shadowed_parameter;
    H::VarDecl global_x;
    global_x.name = "x";
    global_x.sort = H::Sort::integer();
    global_x.lower_bound = H::mkInt(7);
    global_x.upper_bound = H::mkInt(7);
    shadowed_parameter.decls.push_back(global_x);
    H::FunDecl uninterpreted_zero;
    uninterpreted_zero.name = "u";
    uninterpreted_zero.result = H::Sort::integer();
    shadowed_parameter.funs.push_back(std::move(uninterpreted_zero));
    H::FunDecl shadowed_f = defined(
        "f", "x",
        H::mkOp(H::Op::ADD, {H::mkBoundVar("x", H::Sort::integer()),
                             H::mkIdent("x", H::Sort::integer()),
                             H::mkApply("zero", H::Sort::integer(), {})}), true);
    shadowed_parameter.funs.push_back(std::move(shadowed_f));
    H::FunDecl zero;
    zero.name = "zero";
    zero.result = H::Sort::integer();
    zero.body = H::mkApply("u", H::Sort::integer(), {});
    zero.auxiliary = true;
    shadowed_parameter.funs.push_back(std::move(zero));
    H::Constraint constrain_u;
    constrain_u.formula = H::mkOp(
        H::Op::EQ, {H::mkApply("u", H::Sort::integer(), {}), H::mkInt(0)});
    shadowed_parameter.constraints.push_back(std::move(constrain_u));
    H::Constraint shadowed_call;
    shadowed_call.formula = H::mkOp(
        H::Op::EQ,
        {H::mkApply("f", H::Sort::integer(), {H::mkInt(2)}), H::mkInt(9)});
    shadowed_parameter.constraints.push_back(std::move(shadowed_call));
    VERIFY(accepted(shadowed_parameter));
    auto shadowed_translation = SOMTParser::translate(shadowed_parameter);
    VERIFY(shadowed_translation.ok());
    const std::string shadowed_smt = shadowed_translation.toSmt2();
    VERIFY(shadowed_smt.find("(define-fun f ((__somt_hir_param_0 Int)) Int")
           != std::string::npos);
    VERIFY(shadowed_smt.find("(define-fun zero () Int u)") != std::string::npos);
    VERIFY(shadowed_smt.find("(define-fun zero () Int")
           < shadowed_smt.find("(define-fun f "));
    VERIFY(shadowed_smt.find("(declare-fun x () Int)") != std::string::npos);

    // Quoting changes a token spelling, not the symbol's identity. A quoted
    // global that matches the first generated parameter name must force the
    // allocator to skip that name too.
    H::ConstraintModel quoted_collision;
    H::VarDecl quoted_global;
    quoted_global.name = "|__somt_hir_param_0|";
    quoted_global.sort = H::Sort::integer();
    quoted_global.lower_bound = H::mkInt(7);
    quoted_global.upper_bound = H::mkInt(7);
    quoted_collision.decls.push_back(std::move(quoted_global));
    H::FunDecl quoted_f = defined(
        "f", "y",
        H::mkOp(H::Op::ADD, {H::mkBoundVar("y", H::Sort::integer()),
                             H::mkIdent("|__somt_hir_param_0|", H::Sort::integer())}),
        true);
    quoted_collision.funs.push_back(std::move(quoted_f));
    H::Constraint quoted_sat;
    quoted_sat.formula = H::mkOp(
        H::Op::EQ,
        {H::mkApply("f", H::Sort::integer(), {H::mkInt(2)}), H::mkInt(9)});
    quoted_collision.constraints.push_back(std::move(quoted_sat));
    VERIFY(accepted(quoted_collision));
    auto quoted_translation = SOMTParser::translate(quoted_collision);
    VERIFY(quoted_translation.ok());
    const std::string quoted_smt = quoted_translation.toSmt2();
    // This compatibility mode is intentionally usable with the pre-fix lowerer:
    // it exports the buggy candidate's actual script without asserting which
    // formal spelling was chosen, so an independent solver can demonstrate the
    // capture before the freshness fix is applied.
    if (argc == 3 && std::string(argv[1]) == "--emit-quoted-solver-fixtures") {
        namespace fs = std::filesystem;
        const fs::path directory(argv[2]);
        std::error_code error;
        fs::create_directories(directory, error);
        if (error) { return 2; }
        H::ConstraintModel quoted_unsat_model = quoted_collision;
        quoted_unsat_model.constraints.back().formula = H::mkOp(
            H::Op::EQ,
            {H::mkApply("f", H::Sort::integer(), {H::mkInt(2)}), H::mkInt(10)});
        auto quoted_unsat_translation = SOMTParser::translate(quoted_unsat_model);
        if (!quoted_unsat_translation.ok()) { return 3; }
        const std::vector<std::pair<std::string, std::string>> fixtures = {
            {"defined_function_quoted_shadow_sat.smt2", quoted_smt},
            {"defined_function_quoted_shadow_unsat.smt2",
             quoted_unsat_translation.toSmt2()},
        };
        for (const auto& fixture : fixtures) {
            std::ofstream output(directory / fixture.first, std::ios::binary);
            if (!output) { return 4; }
            output << fixture.second;
            output.close();
            if (!output) { return 4; }
        }
        return 0;
    }
    VERIFY(quoted_smt.find("(define-fun f ((__somt_hir_param_1 Int)) Int")
           != std::string::npos);
    VERIFY(quoted_smt.find("(declare-fun |__somt_hir_param_0| () Int)")
           != std::string::npos);

    // Reserved-name aliases use the same canonical identity check. Renaming a
    // reserved function to `not!0` would collide with the quoted source symbol
    // `|not!0|`, so that alias must be skipped.
    H::ConstraintModel quoted_alias_collision;
    H::FunDecl reserved_function;
    reserved_function.name = "not";
    reserved_function.params = {H::Sort::integer()};
    reserved_function.result = H::Sort::boolean();
    quoted_alias_collision.funs.push_back(std::move(reserved_function));
    H::FunDecl quoted_alias;
    quoted_alias.name = "|not!0|";
    quoted_alias.params = {H::Sort::integer()};
    quoted_alias.result = H::Sort::boolean();
    quoted_alias_collision.funs.push_back(std::move(quoted_alias));
    H::VarDecl alias_x;
    alias_x.name = "alias_x";
    alias_x.sort = H::Sort::integer();
    quoted_alias_collision.decls.push_back(std::move(alias_x));
    H::Constraint alias_calls;
    alias_calls.formula = H::mkOp(
        H::Op::AND,
        {H::mkApply("not", H::Sort::boolean(),
                    {H::mkIdent("alias_x", H::Sort::integer())}),
         H::mkApply("|not!0|", H::Sort::boolean(),
                    {H::mkIdent("alias_x", H::Sort::integer())})});
    quoted_alias_collision.constraints.push_back(std::move(alias_calls));
    VERIFY(accepted(quoted_alias_collision));
    auto quoted_alias_translation = SOMTParser::translate(quoted_alias_collision);
    VERIFY(quoted_alias_translation.ok());
    const std::string quoted_alias_smt = quoted_alias_translation.toSmt2();
    VERIFY(quoted_alias_smt.find("not!1") != std::string::npos);
    VERIFY(quoted_alias_smt.find("|not!0|") != std::string::npos);

    // The optional fixture mode lets qualification run an independent solver on
    // exactly the emitted scripts. It writes SAT witnesses and contradictory
    // UNSAT formulas without requiring a Python HIR builder.
    if (argc == 3 && std::string(argv[1]) == "--emit-solver-fixtures") {
        namespace fs = std::filesystem;
        const fs::path directory(argv[2]);
        std::error_code error;
        fs::create_directories(directory, error);
        if (error) { return 2; }
        H::ConstraintModel unsat_model = shadowed_parameter;
        unsat_model.constraints.back().formula = H::mkOp(
            H::Op::EQ,
            {H::mkApply("f", H::Sort::integer(), {H::mkInt(2)}), H::mkInt(10)});
        auto unsat_translation = SOMTParser::translate(unsat_model);
        if (!unsat_translation.ok()) { return 3; }
        H::ConstraintModel quoted_unsat_model = quoted_collision;
        quoted_unsat_model.constraints.back().formula = H::mkOp(
            H::Op::EQ,
            {H::mkApply("f", H::Sort::integer(), {H::mkInt(2)}), H::mkInt(10)});
        auto quoted_unsat_translation = SOMTParser::translate(quoted_unsat_model);
        if (!quoted_unsat_translation.ok()) { return 3; }
        const std::vector<std::pair<std::string, std::string>> fixtures = {
            {"defined_function_shadow_sat.smt2", shadowed_smt},
            {"defined_function_shadow_unsat.smt2", unsat_translation.toSmt2()},
            {"defined_function_quoted_shadow_sat.smt2", quoted_smt},
            {"defined_function_quoted_shadow_unsat.smt2",
             quoted_unsat_translation.toSmt2()},
        };
        for (const auto& fixture : fixtures) {
            std::ofstream output(directory / fixture.first, std::ios::binary);
            if (!output) { return 4; }
            output << fixture.second;
            output.close();
            if (!output) { return 4; }
        }
        return 0;
    }

    // Reused source parameter spellings with different sorts and a parameter
    // matching another function's name still receive independent emitted names.
    H::ConstraintModel repeated_parameter_names;
    H::FunDecl int_f = defined("f", "shared", H::mkBoundVar("shared", H::Sort::integer()), true);
    H::FunDecl bool_g;
    bool_g.name = "g";
    bool_g.params = {H::Sort::boolean()};
    bool_g.result = H::Sort::boolean();
    bool_g.binders = {{"shared", H::Sort::boolean()}};
    bool_g.body = H::mkBoundVar("shared", H::Sort::boolean());
    bool_g.auxiliary = true;
    H::FunDecl colliding_binder;
    colliding_binder.name = "h";
    colliding_binder.params = {H::Sort::integer()};
    colliding_binder.result = H::Sort::integer();
    colliding_binder.binders = {{"f", H::Sort::integer()}};
    colliding_binder.body = H::mkBoundVar("f", H::Sort::integer());
    colliding_binder.auxiliary = true;
    repeated_parameter_names.funs = {std::move(int_f), std::move(bool_g),
                                     std::move(colliding_binder)};
    VERIFY(accepted(repeated_parameter_names));
    auto repeated_translation = SOMTParser::translate(repeated_parameter_names);
    VERIFY(repeated_translation.ok());
    const std::string repeated_smt = repeated_translation.toSmt2();
    VERIFY(repeated_smt.find("(define-fun f ((__somt_hir_param_0 Int)) Int")
           != std::string::npos);
    VERIFY(repeated_smt.find("(define-fun g ((__somt_hir_param_1 Bool)) Bool")
           != std::string::npos);
    VERIFY(repeated_smt.find("(define-fun h ((__somt_hir_param_2 Int)) Int")
           != std::string::npos);

    H::ConstraintModel wrong_sort = twoHelpers();
    wrong_sort.funs.front().binders.front().sort = H::Sort::boolean();
    VERIFY(!accepted(wrong_sort));

    H::ConstraintModel missing_binder = twoHelpers();
    missing_binder.funs.front().body = H::mkBoundVar("missing", H::Sort::integer());
    VERIFY(!accepted(missing_binder));

    H::ConstraintModel free_identifier = twoHelpers();
    free_identifier.funs.front().body = H::mkIdent("not_declared", H::Sort::integer());
    VERIFY(!accepted(free_identifier));

    H::ConstraintModel wrong_result = twoHelpers();
    wrong_result.funs.front().body = H::mkBool(true);
    VERIFY(!accepted(wrong_result));

    H::ConstraintModel recursive = twoHelpers();
    recursive.funs[1].body = H::mkApply(
        "f", H::Sort::integer(), {H::mkBoundVar("z", H::Sort::integer())});
    VERIFY(!accepted(recursive));

    H::ConstraintModel unsupported_global;
    H::FunDecl global_function;
    global_function.name = "predicate";
    global_function.result = H::Sort::boolean();
    global_function.body = H::mkGlobal("unsupported-inside-definition", {});
    unsupported_global.funs.push_back(std::move(global_function));
    VERIFY(!accepted(unsupported_global));

    // Hiding an uninterpreted function is not a sound projection: its arbitrary
    // interpretation could make a target formula true or false independently
    // of the advertised source signature.
    H::ConstraintModel uninterpreted_auxiliary;
    H::FunDecl hidden_uninterpreted;
    hidden_uninterpreted.name = "hidden";
    hidden_uninterpreted.params = {H::Sort::integer()};
    hidden_uninterpreted.result = H::Sort::boolean();
    hidden_uninterpreted.auxiliary = true;
    uninterpreted_auxiliary.funs.push_back(std::move(hidden_uninterpreted));
    const auto hidden_call = H::mkApply(
        "hidden", H::Sort::boolean(), {H::mkInt(0)});
    H::Constraint hidden_contradiction;
    hidden_contradiction.formula = H::mkOp(
        H::Op::AND, {hidden_call, H::mkOp(H::Op::NOT, {hidden_call})});
    uninterpreted_auxiliary.constraints.push_back(std::move(hidden_contradiction));
    VERIFY(!accepted(uninterpreted_auxiliary));

    // IDENT must match the full declared sort, not just SortKind. Otherwise a
    // stale HIR sort reaches lowering as the declaration's real DAG sort and
    // can produce an ill-sorted SMT definition (for example BV4 used as BV8).
    VERIFY(rejectsStaleIdentSort(H::Sort::bitvec(4), H::Sort::bitvec(8)));
    VERIFY(!rejectsStaleIdentSort(H::Sort::bitvec(4), H::Sort::bitvec(4)));
    VERIFY(rejectsStaleIdentSort(
        H::Sort::array(H::Sort::integer(), H::Sort::integer()),
        H::Sort::array(H::Sort::boolean(), H::Sort::integer())));
    VERIFY(rejectsStaleIdentSort(
        H::Sort::array(H::Sort::integer(), H::Sort::integer()),
        H::Sort::array(H::Sort::integer(), H::Sort::boolean())));

    H::ConstraintModel parametric_sort;
    parametric_sort.uninterpreted_sorts.push_back({"S", 1, {}});
    VERIFY(rejectsStaleIdentSort(
        H::Sort::sortApp("S", {H::Sort::integer()}),
        H::Sort::sortApp("S", {H::Sort::boolean()}), parametric_sort));

    H::ConstraintModel parametric_datatype;
    H::DatatypeDecl box;
    box.name = "Box";
    box.params = {"T"};
    H::DtConstructor make_box;
    make_box.name = "make-box";
    make_box.selectors.push_back({"unbox", H::Sort::uninterpreted("T")});
    box.constructors.push_back(std::move(make_box));
    parametric_datatype.datatypes.push_back(std::move(box));
    VERIFY(rejectsStaleIdentSort(
        H::Sort::datatype("Box", {H::Sort::integer()}),
        H::Sort::datatype("Box", {H::Sort::boolean()}), parametric_datatype));
    return 0;
}
