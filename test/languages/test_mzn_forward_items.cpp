// Order-independent MiniZinc finite sets and test/predicate operations.
#include "somtparser/translation/translate.h"
#include "somtparser/languages/minizinc.h"
#include "somtparser/languages/register_all.h"
#include "test_helpers.h"

#include <cassert>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation run(const std::string& source) {
    Lang::SourceUnit unit;
    unit.main_path = "forward.mzn";
    unit.display_name = unit.main_path;
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

Translation runFile(const std::filesystem::path& path) {
    Lang::SourceUnit unit;
    unit.main_path = path.string();
    unit.display_name = unit.main_path;
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& needle) {
    return text.find(needle) != std::string::npos;
}

} // namespace

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // Both the set value and its test operation follow their first uses.
    // The finite set must be elaborated before `x`'s earlier constraint is
    // parsed, and the test body must be available while folding its set
    // comprehension. This is not an unconstrained placeholder set.
    {
        const Translation result = run(
            "set of int: universe = 0..3;\n"
            "set of int: selected;\n"
            "var 0..3: x;\n"
            "constraint x in selected;\n"
            "selected = {i | i in universe where keep(i)};\n"
            "test keep(int: i) = i > 1;\n"
            "solve satisfy;\n");
        VERIFY(result.ok());
        const std::string smt = result.toSmt2();
        VERIFY(has(smt, "(assert"));
        VERIFY(!has(smt, "declare-fun keep"));
        VERIFY(result.report().stats().num_vars == 1);
        bool asserts_selected_domain = false;
        std::size_t at = 0;
        while ((at = smt.find("(assert", at)) != std::string::npos) {
            const std::size_t end = smt.find('\n', at);
            const std::string line = smt.substr(at, end - at);
            if (has(line, "x") && has(line, "2") && has(line, "3")) {
                asserts_selected_domain = true;
                break;
            }
            at = end == std::string::npos ? smt.size() : end;
        }
        VERIFY(asserts_selected_domain);
    }

    // A definition in an include retains its own lexer/source frame during
    // the prescan and later inlining into the caller's set comprehension.
    {
        const auto nonce = std::chrono::steady_clock::now().time_since_epoch().count();
        const auto root = std::filesystem::temp_directory_path()
            / ("somtparser-mzn-forward-items-260-" + std::to_string(nonce));
        std::filesystem::create_directories(root);
        {
            std::ofstream out(root / "ops.mzn");
            out << "test keep(int: i) = i = 2;\n";
        }
        {
            std::ofstream out(root / "model.mzn");
            out << "include \"ops.mzn\";\n"
                   "set of int: universe = 1..3;\n"
                   "set of int: selected;\n"
                   "selected = {i | i in universe where keep(i)};\n"
                   "var selected: x;\n"
                   "constraint x = 2;\n"
                   "solve satisfy;\n";
        }
        const Translation result = runFile(root / "model.mzn");
        VERIFY(result.ok());
        VERIFY(has(result.toSmt2(), "2"));
        std::filesystem::remove_all(root);
    }
    {
        const auto nonce = std::chrono::steady_clock::now().time_since_epoch().count();
        const auto root = std::filesystem::temp_directory_path()
            / ("somtparser-mzn-forward-cycle-260-" + std::to_string(nonce));
        std::filesystem::create_directories(root);
        {
            std::ofstream out(root / "a.mzn");
            out << "include \"b.mzn\";\nsolve satisfy;\n";
        }
        {
            std::ofstream out(root / "b.mzn");
            out << "include \"a.mzn\";\n";
        }
        const Translation result = runFile(root / "a.mzn");
        VERIFY(!result.ok());
        VERIFY(has(result.diagnostics().all().front().message, "cycle"));
        std::filesystem::remove_all(root);
    }

    // The declaration prepass does not turn missing or cyclic operations into
    // unconstrained calls, and duplicate definitions remain errors.
    {
        const Translation missing = run(
            "set of int: universe = 1..2;\n"
            "set of int: selected = {i | i in universe where missing_test(i)};\n"
            "var selected: x;\nsolve satisfy;\n");
        VERIFY(!missing.ok());
    }
    {
        // MiniZinc permits the implicit Bool-to-Int coercion for a fixed
        // operation argument. String remains an incompatible actual type.
        const Translation coerced_bool = run(
            "test keep(int: i) = i > 0;\n"
            "constraint keep(true);\nsolve satisfy;\n");
        VERIFY(coerced_bool.ok());
        const Translation wrong_sort = run(
            "test keep(int: i) = i > 0;\n"
            "constraint keep(\"true\");\nsolve satisfy;\n");
        VERIFY(!wrong_sort.ok());
    }
    // A MiniZinc test is a fixed `par bool` computation, not a predicate
    // whose truth can vary with a decision assignment.
    {
        const Translation decision_dependent = run(
            "var bool: decision;\n"
            "test invalid() = decision;\n"
            "constraint invalid();\nsolve satisfy;\n");
        VERIFY(!decision_dependent.ok());
        VERIFY(has(decision_dependent.diagnostics().all().front().message,
                   "independent of decision values"));
    }
    {
        const Translation variable_parameter = run(
            "test invalid(var bool: value) = value;\n"
            "var bool: decision;\n"
            "constraint invalid(decision);\nsolve satisfy;\n");
        VERIFY(!variable_parameter.ok());
        VERIFY(has(variable_parameter.diagnostics().all().front().message,
                   "independent of decision values"));
    }
    {
        // MiniZinc permits a var formal when the test result remains par bool.
        const Translation unused_variable_parameter = run(
            "test always(var bool: value) = true;\n"
            "var bool: decision;\n"
            "constraint always(decision);\nsolve satisfy;\n");
        VERIFY(unused_variable_parameter.ok());
    }
    {
        const Translation cycle = run(
            "test left(int: i) = right(i);\n"
            "test right(int: i) = left(i);\n"
            "constraint left(1);\nsolve satisfy;\n");
        VERIFY(!cycle.ok());
        VERIFY(has(cycle.diagnostics().all().front().message, "recurs"));
    }
    {
        const Translation duplicate = run(
            "test keep(int: i) = i > 0;\n"
            "test keep(int: i) = i < 3;\n"
            "var 0..2: x;\nconstraint keep(x);\nsolve satisfy;\n");
        VERIFY(!duplicate.ok());
    }
    {
        const Translation duplicate_set = run(
            "set of int: selected;\n"
            "selected = 1..2;\n"
            "selected = 2..3;\n"
            "var selected: x;\nsolve satisfy;\n");
        VERIFY(!duplicate_set.ok());
    }
    {
        const Translation local_set_domain = run(
            "set of int: D = 1..3;\n"
            "constraint let { set of D: s = {1, 3}; } in card(s) = 2;\n"
            "solve satisfy;\n");
        VERIFY(local_set_domain.ok());
        const Translation out_of_domain = run(
            "set of int: D = 1..3;\n"
            "constraint let { set of D: s = {4}; } in true;\n"
            "solve satisfy;\n");
        VERIFY(out_of_domain.ok());
        const Translation negated_out_of_domain = run(
            "set of int: D = 1..3;\n"
            "constraint not (let { set of D: s = {4}; } in true);\n"
            "solve satisfy;\n");
        VERIFY(negated_out_of_domain.ok());
        const Translation enum_local_set = run(
            "enum E = {A, B};\n"
            "constraint let { set of E: s = {A}; } in A in s;\n"
            "solve satisfy;\n");
        VERIFY(enum_local_set.ok());
        const Translation foreign_enum_local_set = run(
            "enum E = {A, B}; enum F = {C, D};\n"
            "constraint let { set of E: s = {C}; } in true;\n"
            "solve satisfy;\n");
        VERIFY(!foreign_enum_local_set.ok());
    }

    std::cout << "MiniZinc forward-item tests passed.\n";
    return 0;
}
