#include "somtparser/hir/packed_scalar_io.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/translation/translate.h"
#include "somtparser/translation/pass.h"
#include "test_helpers.h"

#include <algorithm>
#include <fstream>
#include <functional>
#include <limits>
#include <sstream>
#include <streambuf>

using namespace SOMTParser;
namespace H = Uir::Hir;

namespace {
class UnawarePass : public Uir::Pass {
public:
    std::string id() const override { return "unaware-scalar"; }
    Uir::PassTraits traits() const override { return {}; }
    bool run(H::ConstraintModel&, Uir::LowerContext&) override { ran = true; return true; }
    bool ran = false;
};
class FailingBuffer : public std::streambuf {
public:
    explicit FailingBuffer(std::size_t limit) : remaining_(limit) {}
    std::streamsize xsputn(const char*, std::streamsize count) override {
        const auto accepted = std::min(remaining_, static_cast<std::size_t>(count));
        remaining_ -= accepted;
        return static_cast<std::streamsize>(accepted);
    }
    int_type overflow(int_type c) override {
        if (traits_type::eq_int_type(c, traits_type::eof())) { return traits_type::not_eof(c); }
        if (!remaining_) { return traits_type::eof(); }
        --remaining_; return c;
    }
private:
    std::size_t remaining_;
};

H::ConstraintModel makeModel(const std::string& variable, const std::string& function,
                             H::ObjKind direction) {
    H::ConstraintModel model;
    H::ScalarVarRange range;
    range.prefix = "pos[3]["; range.first = 7; range.count = 5;
    range.lower_bound = H::mkInt(-2); range.upper_bound = H::mkInt(5);
    range.loc = {"scalars.xml", 4, 1};
    model.scalar_var_ranges.push_back(range);
    H::VarDecl d; d.name = variable; d.sort = H::Sort::integer();
    d.lower_bound = H::mkInt(-9); d.upper_bound = H::mkInt(9);
    model.decls.push_back(d);
    H::FunDecl f; f.name = function; f.params = {H::Sort::integer(), H::Sort::integer()};
    f.result = H::Sort::boolean(); f.auxiliary = true;
    f.binders = {{"u", H::Sort::integer()}, {"v", H::Sort::integer()}};
    f.body = H::mkOp(H::Op::EQ,
        {H::mkOp(H::Op::ADD, {H::mkBoundVar("u", H::Sort::integer()), H::mkInt(1)}),
         H::mkBoundVar("v", H::Sort::integer())});
    model.funs.push_back(f);
    H::FunDecl capture; capture.name = "capture"; capture.params = {H::Sort::integer()};
    capture.result = H::Sort::boolean(); capture.auxiliary = true;
    capture.binders = {{"bound", H::Sort::integer()}};
    capture.body = H::mkOp(H::Op::LE,
        {H::mkBoundVar("bound", H::Sort::integer()), H::mkIdent("pos[3][10]", H::Sort::integer())});
    model.funs.push_back(capture);
    auto calls = std::make_shared<H::PackedFunctionCalls>();
    H::PackedFunctionCallBatch batch;
    batch.function = function; batch.arity = 2; batch.loc = {"scalars.xml", 9, 1};
    batch.constants = {H::mkInt(-1)};
    batch.arguments = {{0, 0}, {H::PackedScalarArgument::DECLARATION, 0},
                       {0, 1}, {H::PackedScalarArgument::CONSTANT, 0}};
    calls->batches.push_back(batch);
    batch.function = "capture"; batch.arity = 1; batch.constants.clear(); batch.arguments = {{0, 0}};
    calls->batches.push_back(batch);
    model.packed_function_calls = calls;
    H::Constraint distinct;
    distinct.formula = H::mkOp(H::Op::DISTINCT,
        {H::mkIdent("pos[3][7]", H::Sort::integer()), H::mkIdent("pos[3][8]", H::Sort::integer())});
    model.constraints.push_back(distinct);
    H::Objective objective;
    objective.name = "cost"; objective.kind = direction;
    objective.term = H::mkOp(H::Op::ADD,
        {H::mkIdent(variable, H::Sort::integer()), H::mkIdent("pos[3][9]", H::Sort::integer())});
    model.objectives.push_back(objective);
    return model;
}

H::ConstraintModel expandedModel(const H::ConstraintModel& compact) {
    auto model = compact;
    model.scalar_var_ranges.clear(); model.packed_function_calls.reset();
    for (const auto& range : compact.scalar_var_ranges) {
        for (std::uint64_t offset = 0; offset < range.count; ++offset) {
            H::VarDecl d; d.name = range.name(offset); d.sort = range.sort;
            d.lower_bound = range.lower_bound; d.upper_bound = range.upper_bound; d.loc = range.loc;
            model.decls.push_back(std::move(d));
        }
    }
    for (const auto& batch : compact.packed_function_calls->batches) {
        for (std::size_t row = 0; row < batch.arguments.size(); row += batch.arity) {
            std::vector<H::ExprPtr> arguments;
            for (std::size_t column = 0; column < batch.arity; ++column) {
                const auto& arg = batch.arguments[row + column];
                if (arg.source == H::PackedScalarArgument::DECLARATION) {
                    const auto& d = compact.decls[arg.offset];
                    arguments.push_back(H::mkIdent(d.name, d.sort));
                } else if (arg.source == H::PackedScalarArgument::CONSTANT) {
                    arguments.push_back(batch.constants[arg.offset]);
                } else {
                    const auto& range = compact.scalar_var_ranges[arg.source];
                    arguments.push_back(H::mkIdent(range.name(arg.offset), range.sort));
                }
            }
            H::Constraint constraint;
            constraint.loc = batch.loc;
            constraint.formula = H::mkApply(batch.function, H::Sort::boolean(), std::move(arguments), batch.loc);
            model.constraints.push_back(std::move(constraint));
        }
    }
    return model;
}
}

int main(int argc, char** argv) {
    std::size_t number = 0;
    for (const auto variable : {"and", "plain variable"}) {
        for (const auto function : {"not", "relation"}) {
            for (const auto direction : {H::ObjKind::MINIMIZE, H::ObjKind::MAXIMIZE}) {
                auto model = makeModel(variable, function, direction);
                const auto storage = model.packed_function_calls;
                Uir::Diagnostics diagnostics;
                VERIFY(H::typeCheck(model, diagnostics));
                const auto& range = model.scalar_var_ranges.front();
                std::uint64_t actual = 0;
                VERIFY(range.contains("pos[3][7]", &actual) && actual == 7);
                VERIFY(range.name(4) == "pos[3][11]");
                VERIFY(!range.contains("pos[3][07]") && !range.contains("pos[3][12]"));
                auto preamble = H::packedScalarPreamble(model, diagnostics);
                VERIFY(preamble && preamble->decls.size() == 5); // unused [11] stays compact
                TranslateOptions options; options.omt_dialect = Lower::OmtDialect::None;
                // Omitting objectives deliberately chooses a feasibility-only
                // view. The default profile must still reject that loss; the
                // retained objectives are exercised by subsequent re-emission.
                if (number == 0) {
                    const auto rejected = translate(model, options);
                    VERIFY(!rejected.ok());
                    const auto& errors = rejected.diagnostics().all();
                    VERIFY(std::any_of(errors.begin(), errors.end(), [](const auto& error) {
                        return error.code == Uir::ErrorCode::E_FIDELITY_REJECTED;
                    }));
                }
                options.profile_id = "feasibility";
                const auto compact = translate(model, options);
                if (!compact.ok()) {
                    for (const auto& d : compact.diagnostics().all()) { std::cerr << d.message << '\n'; }
                }
                VERIFY(compact.ok() && compact.usesPackedSmtStream() && !compact.hasParser());
                VERIFY(compact.report().stats().num_vars == 6);
                VERIFY(compact.objectiveCount() == 1);
                VERIFY(model.packed_function_calls == storage);
                const auto expected = translate(expandedModel(model), options);
                VERIFY(expected.ok());
                const auto output = compact.toSmt2(Lower::OmtDialect::Z3);
                VERIFY(output.rfind("(set-logic ", 0) == 0);
                VERIFY(output.find("pos[3][11]") != std::string::npos);
                const auto plain = compact.toSmt2(Lower::OmtDialect::None);
                VERIFY(plain.find("(minimize ") == std::string::npos && plain.find("(maximize ") == std::string::npos);
                VERIFY(compact.toSmt2(Lower::OmtDialect::SmtLib2025).find("(define-objective cost ") != std::string::npos);
                for (const auto limit : {std::size_t(0), output.size() / 2, output.size() - 1}) {
                    FailingBuffer buffer(limit); std::ostream stream(&buffer);
                    bool failed = false;
                    try { compact.writeSmt2(stream, Lower::OmtDialect::Z3); }
                    catch (const std::runtime_error&) { failed = true; }
                    VERIFY(failed && !stream);
                }
                if (argc == 2) {
                    std::ofstream packed(std::string(argv[1]) + "/case-" + std::to_string(number) + "-packed.smt2");
                    packed << output; VERIFY(packed.good());
                    std::ofstream ordinary(std::string(argv[1]) + "/case-" + std::to_string(number) + "-expanded.smt2");
                    ordinary << expected.toSmt2(Lower::OmtDialect::Z3); VERIFY(ordinary.good());
                }
                ++number;
            }
        }
    }
    const auto reject = [&](const std::function<void(H::ConstraintModel&, H::PackedFunctionCalls&)>& change) {
        auto model = makeModel("x", "f", H::ObjKind::MINIMIZE);
        auto calls = std::make_shared<H::PackedFunctionCalls>(*model.packed_function_calls);
        change(model, *calls); model.packed_function_calls = calls;
        Uir::Diagnostics diagnostics;
        VERIFY(!H::typeCheck(model, diagnostics));
        VERIFY(diagnostics.hasErrors());
    };
    reject([](auto& m, auto&) { m.scalar_var_ranges.push_back(m.scalar_var_ranges[0]); });
    reject([](auto& m, auto&) { m.scalar_var_ranges[0].first = UINT64_MAX; });
    reject([](auto& m, auto&) { m.scalar_var_ranges[0].suffix = ""; });
    reject([](auto& m, auto&) { m.scalar_var_ranges[0].lower_bound = H::mkBool(false); });
    reject([](auto& m, auto&) { m.decls[0].name = "pos[3][11]"; });
    reject([](auto& m, auto&) { m.decls[0].name = "|pos[3][11]|"; });
    reject([](auto& m, auto&) { m.funs[0].name = "pos[3][11]"; });
    reject([](auto& m, auto&) { m.objectives[0].name = "pos[3][11]"; });
    reject([](auto&, auto& c) { c.batches[0].arguments[0].source = 99; });
    reject([](auto&, auto& c) { c.batches[0].arguments[0].offset = 5; });
    reject([](auto&, auto& c) { c.batches[0].arguments[1].offset = 99; });
    reject([](auto&, auto& c) { c.batches[0].arguments.back().offset = 99; });
    reject([](auto&, auto& c) { c.batches[0].constants[0] = H::mkBool(false); });
    reject([](auto&, auto& c) { c.batches[0].function = "undeclared"; });
    reject([](auto&, auto& c) { c.batches[0].arity = 0; });
    reject([](auto&, auto& c) { c.batches[0].arguments.pop_back(); });
    reject([](auto& m, auto&) { m.funs[0].body = H::mkIdent("unbound", H::Sort::boolean()); });

    // Match the ordinary HIR namespace rules, including generated datatype
    // recognizers: these collision checks must not depend on a term using it.
    for (int kind = 0; kind < 5; ++kind) {
        H::ConstraintModel collision;
        auto range = makeModel("x", "f", H::ObjKind::MINIMIZE).scalar_var_ranges.front();
        H::DatatypeDecl datatype; datatype.name = "Shape";
        H::DtConstructor constructor; constructor.name = "C";
        if (kind == 0) { collision.uninterpreted_sorts.push_back({"pos[3][11]", 0, {}}); }
        if (kind == 1) { datatype.name = "pos[3][11]"; }
        if (kind == 2) { constructor.name = "pos[3][11]"; }
        if (kind == 3) { constructor.selectors.push_back({"pos[3][11]", H::Sort::integer()}); }
        if (kind == 4) { range.prefix = "is-pos[3]["; constructor.name = "pos[3][11]"; }
        datatype.constructors.push_back(std::move(constructor));
        collision.datatypes.push_back(std::move(datatype));
        collision.scalar_var_ranges.push_back(std::move(range));
        Uir::Diagnostics collision_errors;
        VERIFY(!H::validatePackedScalarModel(collision, collision_errors));
        VERIFY(collision_errors.hasErrors());
    }

    auto model = makeModel("x", "f", H::ObjKind::MINIMIZE);
    Uir::PassRegistry registry;
    auto unaware = std::make_shared<UnawarePass>(); registry.add(unaware);
    auto profile = Uir::EncodingProfile::make("unaware-scalar-test", {{unaware->id(), {}}}, Uir::Fidelity::exact());
    Uir::Diagnostics diagnostics; Uir::TranslationReport report;
    VERIFY(!Uir::PassManager::run(model, *profile, registry, report, diagnostics));
    VERIFY(!unaware->ran);
    Lower::HirToParser lowerer(newParser()); Uir::Diagnostics ordinary_errors;
    VERIFY(!lowerer.lower(model, report, ordinary_errors));
    return 0;
}
