// A MiniZinc model is not one file, and its items are not ordered.
//
// Two facts about the language that a single-pass reader gets wrong in the same
// way, and both of them reject LEGAL MODELS rather than decline a construct:
//
//   * `include "m.model";` brings in model content. Refusing it and translating
//     what is left answers a different question -- and eleven of the sixteen
//     files in libminizinc's own example set are exactly this shape, an
//     instance file that is nothing but an include and an assignment.
//
//   * items are UNORDERED. Those same files put the include first and the
//     assignment after it, so the model uses `n` in `array[1..n]` before `n =
//     3;` appears. The value is needed at PARSE time -- the index set decides
//     how many variables are declared -- so it cannot be applied afterwards the
//     way a solver applies one. Hence the assignment pre-pass.
//
// The `.dzn` half is the same mechanism pointed at a second file: `int: n;` in
// the model and `n = 8;` in the data.
//
// What this file does NOT assert is that the corpus count went up. It did not,
// immediately: every one of those eleven files now fails on something deeper
// (2-D arrays, `set` items, annotations). That is the point of a corpus -- the
// failure distribution moves and the next gap becomes visible -- and the
// per-construct cases below are what pins the layer that was fixed.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

const char* kDir = "languages/minizinc/instances/ok/multifile/";

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation run(const std::string& main, const std::vector<std::string>& data = {}) {
    Lang::SourceUnit u;
    u.main_path = main;
    u.display_name = main;
    u.data_paths = data;
    TranslateOptions opts;
    opts.language_id = "minizinc";
    return translate(u, opts);
}

std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    return "";
}

} // namespace

int main() {
    std::cout << "======= MiniZinc: include, data files, item order =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- include, with the assignment AFTER it. -----------------------------
    {
        const Translation t = run(std::string(kDir) + "instance.mzn");
        if (!t.ok()) {
            std::cout << "  multi-file instance refused: " << firstError(t) << "\n";
            VERIFY(false);
        }
        const std::string smt = t.toSmt2();
        // `n = 4` reached `array[1..n]`, which is only possible if the
        // assignment was read before the declaration that uses it.
        VERIFY(has(smt, "(select q 4)"));
        VERIFY(!has(smt, "(select q 5)"));
        ParserPtr p = newParser();
        VERIFY(p->parseStr(smt));
    }

    // ---- The same model, its value from a .dzn. -----------------------------
    {
        const Translation t = run(std::string(kDir) + "needs_data.mzn",
                                  {std::string(kDir) + "data.dzn"});
        if (!t.ok()) {
            std::cout << "  data file refused: " << firstError(t) << "\n";
            VERIFY(false);
        }
        // The data says 5, so the fifth cell exists and there is no sixth.
        // This is what distinguishes "the data was read" from "the data was
        // accepted and ignored", which would translate the model with some
        // other n and report success.
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(select q 5)"));
        VERIFY(!has(smt, "(select q 6)"));
    }
    {
        // Without the data file the same model is REFUSED, not translated with
        // a guessed n. A model missing its data is not a smaller problem.
        const Translation t = run(std::string(kDir) + "needs_data.mzn");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "no data file supplies it"));
    }
    {
        // Fixed floats from data retain their exact rational value; 1.25e-1 is
        // 1/8, not the nearest binary double.
        const Translation t = run(std::string(kDir) + "float_data.mzn",
                                  {std::string(kDir) + "float_data.dzn"});
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(/ 1 8)"));
    }

    // ---- Official MiniZinc JSON data, including a set range. ---------------
    {
        const Translation t = run(std::string(kDir) + "json_data.mzn",
                                  {std::string(kDir) + "json_data.json"});
        if (!t.ok()) {
            std::cout << "  JSON data file refused: " << firstError(t) << "\n";
            VERIFY(false);
        }
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(= x 2)") || has(smt, "(= 2 x)"));
        // Fixed membership is constant-folded; equality orientation is not
        // part of the input contract. The JSON cube's [2,1,2] cell is 6.
        // Python's independent solver oracle checks the complete relation.
        // A singleton interval can be emitted as equality instead of two
        // bounds. The independent Python XOR check covers the full relation,
        // including the hole at 6 and all three values of the second interval.
        VERIFY(has(smt, "(= y 5)") || has(smt, "(= 5 y)")
               || (has(smt, "(>= y 5)") && has(smt, "(<= y 5)")));
        VERIFY(has(smt, "(>= y 7)"));
        VERIFY(has(smt, "(<= y 9)"));
        VERIFY(has(smt, "(= z 6)") || has(smt, "(= 6 z)"));
    }
    {
        const Translation t = run(std::string(kDir) + "json_data.mzn",
                                  {"languages/minizinc/instances/reject/json_ragged_array.json"});
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "parameter array")
               || has(firstError(t), "rectangular"));
    }
    {
        const Translation t = run(
            "languages/minizinc/instances/reject/json_ragged_int_matrix.mzn",
            {"languages/minizinc/instances/reject/json_ragged_int_matrix.json"});
        VERIFY(!t.ok());
    }
    {
        // JSON's tagged enum value is not an ordinary string, even though an
        // untagged JSON string can be coerced to an enum parameter.
        const Translation t = run(
            "languages/minizinc/instances/reject/json_tagged_enum_as_string.mzn",
            {"languages/minizinc/instances/reject/json_tagged_enum_as_string.json"});
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "tagged JSON enum"));
    }
    {
        // The same multidimensional integer array, sparse/ranged sets, and
        // array-of-set values arrive once as official JSON and once as DZN.
        // Equal emitted constraints pin the representation before the parent
        // runs both scripts through its independent Z3 oracle.
        const std::string model = std::string(kDir) + "json_equiv.mzn";
        const Translation from_json = run(model, {std::string(kDir) + "json_equiv.json"});
        const Translation from_dzn = run(model, {std::string(kDir) + "json_equiv.dzn"});
        if (!from_json.ok()) {
            std::cout << "  JSON equivalence fixture refused: " << firstError(from_json) << "\n";
            VERIFY(false);
        }
        if (!from_dzn.ok()) {
            std::cout << "  DZN equivalence fixture refused: " << firstError(from_dzn) << "\n";
            VERIFY(false);
        }
        VERIFY(from_json.toSmt2() == from_dzn.toSmt2());
    }

    // ---- A parameter ARRAY from the same data file. -------------------------
    //
    // `.dzn` support landed for scalars and stopped there: parseDataValue bound
    // an array literal into par_arrays_ and the DECLARATION never asked, so
    // `array[1..3] of int: w;` was refused with "this frontend does not read
    // [a .dzn]" by a frontend that had just read one. Half a feature, and the
    // error message froze at the text from before the other half.
    {
        const Translation t = run(std::string(kDir) + "needs_array_data.mzn",
                                  {std::string(kDir) + "array_data.dzn"});
        if (!t.ok()) {
            std::cout << "  array data refused: " << firstError(t) << "\n";
            VERIFY(false);
        }
        // w = [3, 7, 5] on 1..3 and `x > w[2]`, so the bound is 7.
        // Asserting the VALUE rather than merely that it translated is what
        // separates "the data was read" from "the data was accepted and
        // ignored" -- the second also reports success.
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(> x 7)"));
        ParserPtr p = newParser();
        VERIFY(p->parseStr(smt));
    }
    {
        // The explicit array1d data carries the same 0..2 axes as the model.
        // Checking w[2] confirms both the source index set and selected value.
        const Translation t = run(std::string(kDir) + "rebased_array_data.mzn",
                                  {std::string(kDir) + "indexed_array_data.dzn"});
        if (!t.ok()) {
            std::cout << "  explicitly indexed array refused: " << firstError(t) << "\n";
            VERIFY(false);
        }
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(> x 5)"));
        VERIFY(!has(smt, "(> x 7)"));
    }
    {
        // Four declared, three supplied. The length check already guarded a
        // value written in the model; one arriving from a data file meets it
        // too, because what it prevents is the same wrong answer.
        const Translation t = run(std::string(kDir) + "short_array_data.mzn",
                                  {std::string(kDir) + "array_data.dzn"});
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "but is given 3"));
    }
    {
        // And with no data file at all it stays refused -- the point of the fix
        // is that the frontend USES what it read, not that it stops asking.
        const Translation t = run(std::string(kDir) + "needs_array_data.mzn");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "no data file supplies it"));
    }

    // ---- The refusals that must stay refusals. ------------------------------
    {
        // A cycle is not a deep model. Left unchecked this recurses until the
        // stack runs out, which is a crash rather than a diagnostic.
        const Translation t = run(std::string(kDir) + "cycle_a.mzn");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "cycle"));
    }
    {
        // A data file holds assignments. A `constraint` in one would otherwise
        // be dropped silently, and the instance would be weaker than the two
        // files together say.
        const Translation t = run(std::string(kDir) + "needs_data.mzn",
                                  {std::string(kDir) + "bad_data.dzn"});
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "model item"));
    }
    {
        // A missing include names the file. Reporting "unexpected token" here
        // would point at the line after it.
        const Translation t = run(std::string(kDir) + "missing_include.mzn");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "nosuchfile.mzn"));
    }
    {
        // A standard-library include is still skipped rather than read: this
        // frontend recognises `alldifferent` by name and chooses an encoding,
        // so reading MiniZinc's own definition of it would refuse models that
        // work. `stdlib.mzn` reaches a solve item, which proves the include
        // did not abort the parse.
        const Translation t = run(std::string(kDir) + "stdlib.mzn");
        VERIFY(t.ok());
    }

    // ---- One declaration only, however the value arrives. -------------------
    {
        // `n = 3;` beside `int: n;` is one parameter, not two, so the
        // pre-pass binding must not read as a redeclaration -- and a genuine
        // second declaration must still be caught.
        const Translation t = run(std::string(kDir) + "double_decl.mzn");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "already declared"));
    }

    std::cout << "All MiniZinc multi-file tests passed." << std::endl;
    return 0;
}
