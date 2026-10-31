#include "somtparser/languages/minizinc.h"
#include "test_helpers.h"

#include <chrono>
#include <filesystem>
#include <fstream>
#include <set>
#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

namespace {

struct Files {
    std::filesystem::path root;
    Files() {
        root = std::filesystem::temp_directory_path()
            / ("somt-mzn-include-" + std::to_string(
                std::chrono::steady_clock::now().time_since_epoch().count()));
        VERIFY(std::filesystem::create_directory(root));
        std::filesystem::create_directory(root / "nested");
    }
    ~Files() {
        std::error_code ignored;
        std::filesystem::remove_all(root, ignored);
    }
    void write(const std::string& name, const std::string& source) const {
        std::ofstream stream(root / name);
        stream << source;
        VERIFY(stream.good());
    }
};

Lang::ParseOutcome parse(const std::string& source) {
    Lang::SourceUnit unit;
    unit.inline_source = source;
    unit.display_name = "<iterative-minizinc>";
    return Lang::mkMiniZincLanguage()->parse(unit, {});
}

Lang::ParseOutcome parseFile(const std::filesystem::path& path) {
    Lang::SourceUnit unit;
    unit.main_path = path.string();
    unit.display_name = unit.main_path;
    return Lang::mkMiniZincLanguage()->parse(unit, {});
}

void requireSuccess(const Lang::ParseOutcome& result) {
    for (const auto& d : result.diagnostics.all()) {
        if (d.severity == Uir::Severity::ERROR) std::cerr << d.message << '\n';
    }
    VERIFY(result.ok());
}

} // namespace

int main() {
    Files files;
    constexpr int includes = 160;
    for (int i = 0; i < includes; ++i) {
        std::string source = i + 1 == includes ? "var 0..5: x;\n"
            : "include \"frame" + std::to_string(i + 1) + ".mzn\";\n";
        // Same local source name in every restored lexer frame must still
        // produce distinct decision arrays and leave the outer scalar intact.
        source += "constraint let {array[1..1] of var 0..5: local} "
                  "in local[1] >= 0;\nconstraint x >= 0;\n";
        files.write("nested/frame" + std::to_string(i) + ".mzn", source);
    }
    files.write("root.mzn", "include \"nested/frame0.mzn\";\n"
                            "constraint x = 3;\nsolve satisfy;\n");
    {
        const auto result = parseFile(files.root / "root.mzn");
        requireSuccess(result);
        std::set<std::string> locals;
        int outer = 0;
        for (const auto& declaration : result.model->decls) {
            if (declaration.name == "x") ++outer;
            if (declaration.name.find("@let") != std::string::npos) {
                VERIFY(locals.insert(declaration.name).second);
            }
        }
        VERIFY(outer == 1);
        VERIFY(locals.size() == includes);
        bool root_location = false, leaf_location = false;
        for (const auto& constraint : result.model->constraints) {
            root_location |= constraint.loc.file == (files.root / "root.mzn").string();
            leaf_location |= constraint.loc.file ==
                (files.root / "nested/frame159.mzn").string();
        }
        VERIFY(root_location);
        VERIFY(leaf_location);
    }
    {
        // The EOF belongs to the included lexer, even after many callers.
        files.write("nested/frame159.mzn", "var 0..5: x;\n/* never closed");
        const auto result = parseFile(files.root / "root.mzn");
        VERIFY(!result.ok());
        bool located = false;
        for (const auto& diagnostic : result.diagnostics.all()) {
            if (diagnostic.message.find("unterminated block comment") != std::string::npos) {
                VERIFY(diagnostic.loc.file == (files.root / "nested/frame159.mzn").string());
                VERIFY(diagnostic.loc.line == 2);
                located = true;
            }
        }
        VERIFY(located);
    }
    {
        files.write("nested/frame159.mzn", "include \"../root.mzn\";\n");
        const auto result = parseFile(files.root / "root.mzn");
        VERIFY(!result.ok());
        bool cycle = false;
        for (const auto& d : result.diagnostics.all()) {
            cycle |= d.message.find("cycle") != std::string::npos;
        }
        VERIFY(cycle);
        // An ended include is no longer active. Re-reading it is legal.
        files.write("leaf.mzn", "constraint true;\n");
        files.write("repeat.mzn", "include \"leaf.mzn\"; include \"leaf.mzn\"; solve satisfy;");
        const auto repeated = parseFile(files.root / "repeat.mzn");
        requireSuccess(repeated);
        VERIFY(repeated.model->constraints.size() == 2);
    }
    {
        constexpr int arms = 20000;
        std::string source = "constraint if false then undeclared ";
        for (int i = 0; i < arms; ++i) source += "elseif false then undeclared ";
        source += "else true endif; solve satisfy;";
        const auto result = parse(source);
        requireSuccess(result);
        VERIFY(result.model->constraints.size() == 1);
        VERIFY(result.model->constraints.front().formula->kind == H::ExprKind::LIT_BOOL);
        VERIFY(result.model->constraints.front().formula->bool_value);
    }
    {
        const auto result = parse("constraint if false then absent "
            "elseif true then false elseif absent then absent "
            "else (if absent then absent endif) endif; solve satisfy;");
        requireSuccess(result);
        VERIFY(result.model->constraints.front().formula->kind == H::ExprKind::LIT_BOOL);
        VERIFY(!result.model->constraints.front().formula->bool_value);
        VERIFY(!parse("constraint if false then absent elseif false then absent; solve satisfy;").ok());
    }
    {
        // Polarity checking follows a deep elaborated Boolean DAG without
        // recursing. A free let local is permitted only in positive contexts.
        std::string source = "var bool: p; constraint (let {var int: w;} in w = 1)";
        for (int i = 0; i < 20000; ++i) source += " /\\ p";
        source += "; solve satisfy;";
        requireSuccess(parse(source));
        const auto negative = parse("constraint not (let {var int: w;} in w = 1); solve satisfy;");
        VERIFY(!negative.ok());
        VERIFY(negative.diagnostics.firstErrorCode() == Uir::ErrorCode::E_TYPE);
    }
    {
        const auto result = parse("array[2..3,4..5] of var 0..9: a; solve satisfy;");
        requireSuccess(result);
        VERIFY(result.semantics.stages().size() == 1);
        const auto& observables = result.semantics.stages().front().projection.observables;
        VERIFY(observables.size() == 4);
        const char* names[] = {"a[2,4]", "a[2,5]", "a[3,4]", "a[3,5]"};
        for (std::size_t i = 0; i < 4; ++i) {
            VERIFY(observables[i].source_name == names[i]);
            VERIFY(observables[i].target_name == "(select a " + std::to_string(i) + ")");
        }
    }
}
