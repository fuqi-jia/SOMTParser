#include "../../languages/minizinc/src/mzn_expression_analysis.h"
#include "somtparser/languages/minizinc.h"
#include "test_helpers.h"

#include <chrono>
#include <filesystem>
#include <fstream>
#include <string>
#include <unordered_map>

using namespace SOMTParser;
namespace H = Uir::Hir;
namespace D = Lang::detail;

int main() {
    const auto condition = H::mkIdent("condition", H::Sort::boolean());
    const auto red = H::mkIdent("red", H::Sort::integer());
    const auto blue = H::mkIdent("blue", H::Sort::integer());
    const auto plain = H::mkInt(7);
    std::unordered_map<H::ExprPtr, std::string> explicit_types;
    std::unordered_map<std::string, std::string> symbol_types{
        {"red", "Colour"}, {"blue", "Colour"}, {"array", "Colour"}};
    const auto enum_type = [&](const H::ExprPtr& e) {
        return D::enumTypeOfExpression(e, explicit_types, symbol_types);
    };
    VERIFY(enum_type(red) == "Colour");
    VERIFY(enum_type(nullptr).empty());
    VERIFY(enum_type(H::mkOp(H::Op::ITE, {condition, red, blue})) == "Colour");
    VERIFY(enum_type(H::mkOp(H::Op::ITE, {condition, red, plain})).empty());
    const auto array = H::mkIdent("array", H::Sort::array(H::Sort::integer(), H::Sort::integer()));
    VERIFY(enum_type(H::mkOp(H::Op::SELECT, {array, plain})) == "Colour");
    const auto annotated = H::mkOp(H::Op::ADD, {red, plain});
    explicit_types[annotated] = "Other";
    VERIFY(enum_type(annotated) == "Other");
    VERIFY(enum_type(H::mkOp(H::Op::ADD, {blue, plain})).empty());
    explicit_types[condition] = "ignored-non-integer";
    VERIFY(enum_type(condition).empty());

    constexpr std::size_t depth = 200000;
    auto chain = red;
    for (std::size_t i = 0; i < depth; ++i) {
        // Every level shares both arms. A tree walk would duplicate the same
        // suffix exponentially; an explicit stack alone is not sufficient.
        chain = H::mkOp(H::Op::ITE, {condition, chain, chain});
    }
    VERIFY(enum_type(chain) == "Colour");
    std::unordered_map<std::string, H::Sort> scope;
    VERIFY(!D::expressionReferencesDecision(chain, scope));
    scope.emplace("unrelated", H::Sort::integer());
    VERIFY(!D::expressionReferencesDecision(chain, scope));
    scope.emplace("red", H::Sort::integer());
    VERIFY(D::expressionReferencesDecision(chain, scope));
    VERIFY(!D::expressionReferencesDecision(nullptr, scope));
    // Different arms at the outermost node must not inherit the shared arm's
    // nominal type. An explicit annotation still takes precedence.
    const auto mixed = H::mkOp(H::Op::ITE, {condition, chain, annotated});
    VERIFY(enum_type(mixed).empty());
    explicit_types[mixed] = "Override";
    VERIFY(enum_type(mixed) == "Override");

    // An empty list still typechecks its generator body against a nominal
    // default record. Building that default must follow record nesting with
    // continuations, including side fields and repeated schema references.
    const auto directory = std::filesystem::temp_directory_path()
        / ("somt-mzn-analysis-" + std::to_string(
            std::chrono::steady_clock::now().time_since_epoch().count()));
    VERIFY(std::filesystem::create_directory(directory));
    const auto path = directory / "input.json";
    { std::ofstream data(path); data << "{\"wrapper\":{\"items\":[]}}"; VERIFY(data.good()); }
    constexpr std::size_t record_depth = 10000;
    std::string source = "type Leaf=record(int:value,list of int:extras);"
        "type R0=record(Leaf:leaf,Leaf:other);";
    for (std::size_t i = 1; i <= record_depth; ++i) {
        source += "type R" + std::to_string(i) + "=record(bool:flag,R"
            + std::to_string(i - 1) + ":next);";
    }
    source += "type Wrapper=record(list of R" + std::to_string(record_depth)
        + ":items);Wrapper:wrapper;constraint forall(r in wrapper.items)(r";
    for (std::size_t i = 0; i < record_depth; ++i) source += ".next";
    const auto parse = [&](const std::string& suffix) {
        Lang::SourceUnit unit;
        unit.inline_source = source + suffix;
        unit.display_name = "<iterative-analysis>";
        unit.data_paths = {path.string()};
        return Lang::mkMiniZincLanguage()->parse(unit, {});
    };
    const auto result = parse(".leaf.value=0);solve satisfy;");
    for (const auto& diagnostic : result.diagnostics.all()) {
        if (diagnostic.severity == Uir::Severity::ERROR) std::cerr << diagnostic.message << '\n';
    }
    VERIFY(result.ok());
    bool vacuous = false;
    for (const auto& constraint : result.model->constraints) {
        const auto& value = constraint.formula;
        vacuous |= value->kind == H::ExprKind::LIT_BOOL && value->bool_value;
    }
    VERIFY(vacuous);
    const auto invalid = parse(".leaf.missing=0);solve satisfy;");
    VERIFY(!invalid.ok()); // Empty iteration must not hide a malformed body.
    std::error_code ignored;
    std::filesystem::remove_all(directory, ignored);
}
