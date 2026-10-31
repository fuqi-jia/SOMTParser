// Data-file arrayNd constructors can refer to fixed index sets declared in
// the model, which is parsed after the data file. Preserve and check those
// explicit index sets instead of treating them as lengths or rebasing them.

#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <atomic>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation mznWithData(const std::string& source, const std::string& data) {
    static std::atomic<unsigned long long> serial{0};
    const auto stamp = std::chrono::steady_clock::now().time_since_epoch().count();
    const std::filesystem::path path = std::filesystem::temp_directory_path()
        / ("somt-mzn-deferred-array-" + std::to_string(stamp) + "-"
           + std::to_string(serial.fetch_add(1)) + ".dzn");
    {
        std::ofstream out(path, std::ios::binary);
        VERIFY(static_cast<bool>(out));
        out << data;
        VERIFY(static_cast<bool>(out));
    }

    Lang::SourceUnit unit;
    unit.inline_source = source;
    unit.display_name = "<deferred-array-index-test>";
    unit.data_paths.push_back(path.string());
    TranslateOptions options;
    options.language_id = "minizinc";
    Translation result = translate(unit, options);
    std::error_code ec;
    std::filesystem::remove(path, ec);
    return result;
}

std::string firstError(const Translation& translation) {
    for (const Diagnostic& diagnostic : translation.diagnostics().all()) {
        if (diagnostic.severity == Severity::ERROR) { return diagnostic.message; }
    }
    return "<no error>";
}

} // namespace

int main() {
    std::cout << "======= MiniZinc: deferred explicit array indices =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        const Translation t = mznWithData(
            "set of int: ROWS = 2..3;\n"
            "set of int: COLS = 4..5;\n"
            "array[ROWS,COLS] of int: M;\n"
            "constraint M[2,4] = 11;\n"
            "constraint M[2,5] = 12;\n"
            "constraint M[3,4] = 21;\n"
            "constraint M[3,5] = 22;\n"
            "solve satisfy;\n",
            "M = array2d(ROWS, COLS, [11, 12, 21, 22]);\n");
        VERIFY(t.ok());
        ParserPtr parser = newParser();
        VERIFY(parser->parseStr(t.toSmt2()));
    }

    {
        // Same extents do not make different explicit index sets equivalent.
        const Translation t = mznWithData(
            "array[0..1,4..5] of int: M;\n"
            "solve satisfy;\n",
            "M = array2d(2..3, 4..5, [11, 12, 21, 22]);\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(firstError(t).find("different index set") != std::string::npos);
    }

    {
        // A DZN list has 1-based indices; its declaration cannot silently
        // move those cells to 0-based indices.
        const Translation t = mznWithData(
            "array[0..1] of int: M;\n"
            "constraint M[0] = 7;\n"
            "solve satisfy;\n",
            "M = [7, 8];\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(firstError(t).find("different index set") != std::string::npos);

        const Translation explicit_indices = mznWithData(
            "array[0..1] of int: M;\n"
            "constraint M[0] = 7;\n"
            "solve satisfy;\n",
            "M = array1d(0..1, [7, 8]);\n");
        VERIFY(explicit_indices.ok());
    }

    {
        // An explicit array1d index set is part of the value and cannot be
        // silently rebased either.
        const Translation t = mznWithData(
            "array[0..1] of int: M;\n"
            "solve satisfy;\n",
            "M = array1d(1..2, [7, 8]);\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    {
        const Translation t = mznWithData(
            "array[1..2] of int: M;\n"
            "solve satisfy;\n",
            "M = array1d(MISSING, [7, 8]);\n");
        VERIFY(!t.ok());
        VERIFY(firstError(t).find("not a known fixed integer set")
               != std::string::npos);
    }

    {
        const Translation t = mznWithData(
            "set of int: S = {1, 3};\n"
            "array[1..2] of int: M;\n"
            "solve satisfy;\n",
            "M = array1d(S, [7, 8]);\n");
        VERIFY(!t.ok());
        VERIFY(firstError(t).find("is sparse") != std::string::npos);
    }

    {
        // An empty index dimension has zero cells; it is not replaced by a
        // guessed 1-based range while its model name is deferred.
        const Translation t = mznWithData(
            "set of int: ROWS = {};\n"
            "set of int: COLS = 1..2;\n"
            "array[ROWS,COLS] of int: M;\n"
            "solve satisfy;\n",
            "M = array2d(ROWS, COLS, []);\n");
        VERIFY(t.ok());
    }

    {
        // Bounded integer parameter arrays retain their element range on
        // data-file values (the ATSP color compatibility matrix uses 0..1).
        const Translation t = mznWithData(
            "array[1..2] of 0..1: M;\n"
            "constraint M[1] = 0;\n"
            "constraint M[2] = 1;\n"
            "solve satisfy;\n",
            "M = array1d(1..2, [0, 1]);\n");
        VERIFY(t.ok());
    }

    {
        const Translation t = mznWithData(
            "array[1..2] of 0..1: M;\n"
            "solve satisfy;\n",
            "M = array1d(1..2, [0, 2]);\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(firstError(t).find("outside that domain") != std::string::npos);
    }

    {
        // Named sparse element domains constrain data just like literal
        // ranges; accepting a value in the gap would widen the declaration.
        const Translation t = mznWithData(
            "set of int: D = {1, 3};\n"
            "array[1..1] of D: M;\n"
            "solve satisfy;\n",
            "M = [2];\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(firstError(t).find("outside that domain") != std::string::npos);
    }

    {
        // Bounds may be fixed integer parameters supplied before the model;
        // boolean parameters are not integer range endpoints.
        const Translation t = mznWithData(
            "int: lo; int: hi;\n"
            "array[1..2] of lo..hi: M;\n"
            "solve satisfy;\n",
            "lo = 0; hi = 1; M = [0, 1];\n");
        VERIFY(t.ok());
    }

    return 0;
}
