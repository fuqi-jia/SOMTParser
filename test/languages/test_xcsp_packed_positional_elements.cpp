#include "somtparser/languages/xcsp3.h"
#include "somtparser/hir/packed_scalar_io.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <algorithm>
#include <string>
#include <vector>

using namespace SOMTParser;
namespace H = Uir::Hir;

int main() {
    Lang::SourceUnit unit;
    unit.display_name = "positional.xml";
    unit.inline_source =
        "<instance format=\"XCSP3\" type=\"CSP\">\n"
        "<variables>\n"
        "<array id=\"a\" size=\"[256][256]\" startIndex=\"5\">-2..5</array>\n"
        "<var id=\"b\">-2..5</var>\n"
        "<var id=\"i\">-2..5</var>\n"
        "<var id=\"v\">-2..5</var>\n"
        "</variables>\n"
        "<constraints>\n"
        "<element><list startIndex=\"-1\">a[6][7] b a[6][8]</list><index>i</index><value>v</value></element>\n"
        "<element><list startIndex=\"-1\">a[6][7] b a[6][7]</list><index>a[6][7]</index><value>a[6][7]</value></element>\n"
        "<element><list startIndex=\"2\">b a[6][8] a[6][7]</list><index>i</index><value>v</value></element>\n"
        "<element><list startIndex=\"-1\">a[5][5] b -1</list><index>i</index><value>v</value></element>\n"
        "<element><list startIndex=\"-1\">a[5][5] b a[5][5]</list><index rank=\"first\">i</index><value>v</value></element>\n"
        "</constraints></instance>";
    auto parsed = Lang::mkXcsp3Language()->parse(unit, {});
    VERIFY(parsed.ok());
    if (!parsed.model) { return 1; }
    const auto& model = *parsed.model;
    VERIFY(model.scalar_var_ranges.size() == 256);
    VERIFY(model.packed_function_calls != nullptr);
    if (!model.packed_function_calls) { return 1; }
    const auto& batches = model.packed_function_calls->batches;
    VERIFY(batches.size() == 3);
    if (batches.size() != 3) { return 1; }
    const auto nameOf = [&](const H::PackedScalarArgument& arg) {
        if (arg.source == H::PackedScalarArgument::DECLARATION) {
            return model.decls.at(arg.offset).name;
        }
        return model.scalar_var_ranges.at(arg.source).name(arg.offset);
    };
    const std::vector<std::vector<std::string>> expected = {
        {"a[6][7]", "b", "a[6][8]", "i", "v"},
        {"a[6][7]", "b", "a[6][7]", "a[6][7]", "a[6][7]"},
        {"b", "a[6][8]", "a[6][7]", "i", "v"}
    };
    for (std::size_t row = 0; row < batches.size(); ++row) {
        VERIFY(batches[row].arity == 5);
        VERIFY(batches[row].arguments.size() == 5);
        VERIFY(batches[row].loc.file == unit.display_name);
        VERIFY(batches[row].loc.line == static_cast<int>(9 + row));
        std::vector<std::string> names;
        for (const auto& argument : batches[row].arguments) { names.push_back(nameOf(argument)); }
        VERIFY(names == expected[row]);
    }
    VERIFY(batches[0].function == batches[1].function);
    VERIFY(batches[0].function != batches[2].function);
    // The constant and ranked lookups retain their full ordinary formulas.
    VERIFY(model.constraints.size() == 2);
    Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(model, diagnostics));
    auto preamble = H::packedScalarPreamble(model, diagnostics);
    VERIFY(preamble != nullptr && !diagnostics.hasErrors());
    if (!preamble) { return 1; }
    // Coordinates appearing solely in packed calls must not turn back into
    // native declarations; their full domains remain in the scalar ranges.
    for (const auto& declaration : preamble->decls) {
        VERIFY(declaration.name != "a[6][7]");
        VERIFY(declaration.name != "a[6][8]");
    }
    VERIFY(std::any_of(preamble->decls.begin(), preamble->decls.end(),
                      [](const H::VarDecl& declaration) {
                          return declaration.name == "a[5][5]";
                      }));
    return 0;
}
