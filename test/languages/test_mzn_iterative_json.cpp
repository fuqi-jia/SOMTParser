#include "somtparser/languages/minizinc.h"
#include "test_helpers.h"

#include <chrono>
#include <filesystem>
#include <fstream>
#include <string>
#include <unordered_set>
#include <vector>

using namespace SOMTParser;
namespace H = Uir::Hir;

namespace {

struct DataFile {
    std::filesystem::path directory;
    std::filesystem::path path;
    DataFile() {
        directory = std::filesystem::temp_directory_path() / ("somt-mzn-json-"
            + std::to_string(std::chrono::steady_clock::now().time_since_epoch().count()));
        VERIFY(std::filesystem::create_directory(directory));
        path = directory / "input.json";
    }
    ~DataFile() {
        std::error_code ignored;
        std::filesystem::remove_all(directory, ignored);
    }
    Lang::ParseOutcome parse(const std::string& model, const std::string& data) const {
        { std::ofstream file(path); file << data; VERIFY(file.good()); }
        Lang::SourceUnit unit;
        unit.inline_source = model;
        unit.display_name = "<iterative-json>";
        unit.data_paths = {path.string()};
        return Lang::mkMiniZincLanguage()->parse(unit, {});
    }
};

void requireSuccess(const Lang::ParseOutcome& result) {
    for (const auto& d : result.diagnostics.all()) {
        if (d.severity == Uir::Severity::ERROR) std::cerr << d.message << '\n';
    }
    VERIFY(result.ok());
}

bool hasError(const Lang::ParseOutcome& result, const std::string& fragment) {
    for (const auto& d : result.diagnostics.all()) {
        if (d.severity == Uir::Severity::ERROR && d.message.find(fragment) != std::string::npos)
            return true;
    }
    return false;
}

bool fixesX(const Lang::ParseOutcome& result, const std::string& integer) {
    for (const auto& constraint : result.model->constraints) {
        const auto& e = constraint.formula;
        if (e->kind != H::ExprKind::OP || e->op != H::Op::EQ || e->args.size() != 2) continue;
        for (std::size_t i = 0; i < 2; ++i) {
            if (e->args[i]->kind == H::ExprKind::IDENT && e->args[i]->name == "x"
                && e->args[1-i]->kind == H::ExprKind::LIT_INT
                && e->args[1-i]->name == integer) return true;
        }
    }
    return false;
}

} // namespace

int main() {
    DataFile file;
    constexpr std::size_t depth = 2000;
    std::string model = "type R0 = record(int: value);\n";
    for (std::size_t i = 1; i <= depth; ++i) {
        model += "type R" + std::to_string(i) + " = record(R"
            + std::to_string(i - 1) + ": next);\n";
    }
    model += "R" + std::to_string(depth) + ": entry; var int: x; constraint x = entry";
    for (std::size_t i = 0; i < depth; ++i) model += ".next";
    model += ".value; solve satisfy;";
    std::string json = "{\"entry\":";
    for (std::size_t i = 0; i < depth; ++i) json += "{\"next\":";
    json += "{\"value\":17}";
    json.append(depth + 1, '}');
    {
        const auto result = file.parse(model, json);
        requireSuccess(result);
        VERIFY(fixesX(result, "17"));
    }
    {
        // The typed leaf check survives thousands of record continuations;
        // rejecting it also destroys the entire deep source value tree.
        auto bad = json;
        bad.replace(bad.find(":17"), 3, ":true");
        const auto result = file.parse(model, bad);
        VERIFY(!result.ok());
        VERIFY(hasError(result, "wrong type for record field 'value'"));
    }
    {
        auto bad = json;
        bad.replace(bad.find("\"value\":17"), 10, "\"value\":17,\"value\":18");
        const auto result = file.parse(model, bad);
        VERIFY(!result.ok());
        VERIFY(hasError(result, "duplicate JSON record field 'value'"));
        for (const auto& d : result.diagnostics.all()) {
            if (d.severity == Uir::Severity::ERROR) VERIFY(d.loc.file == file.path.string());
        }
        VERIFY(!file.parse(model, json.substr(0, json.size() - 1)).ok());
    }
    {
        // Arrays, nested records, typed lists, field order, and singleton
        // enum/record tag ambiguity all cross the same continuation stack.
        const auto result = file.parse(
            "enum Shade={blue,red}; type Literal=record(string:e);"
            "type Item=record(int:n);"
            "type Row=record(Shade:shade,Literal:literal,list of Item:items);"
            "Row:row;var int:x;constraint x=row.items[2].n;"
            "constraint row.literal.e=\"blue\";constraint row.shade=blue;solve satisfy;",
            "{\"row\":{\"items\":[{\"n\":4},{\"n\":7}],"
            "\"literal\":{\"e\":\"blue\"},\"shade\":{\"e\":\"blue\"}}}");
        requireSuccess(result);
        VERIFY(fixesX(result, "7"));
    }
    {
        const std::string arrays = "set of int:S;array[1..2,1..2] of int:m;"
            "array[1..2] of set of int:sets;var int:x;constraint x=m[2,1];"
            "constraint 3 in S;constraint 2 in sets[1];solve satisfy;";
        const auto result = file.parse(arrays,
            "{\"S\":{\"set\":[1,[3,5]]},\"m\":[[1,2],[7,4]],\"sets\":[[2],[3,4]]}");
        requireSuccess(result);
        VERIFY(fixesX(result, "7"));
        const auto bad = file.parse("set of int:S;solve satisfy;",
                                    "{\"S\":{\"set\":[[1,2,3]]}}");
        VERIFY(!bad.ok());
        VERIFY(hasError(bad, "pair of integers"));
    }
}
