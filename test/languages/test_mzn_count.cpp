// The `count` global constraint, and the bucket it used to land in.
//
// `count` was not implemented and fell through to the identifier path, so
// three battleships models in the upstream corpus reported
// `E_TYPE: undeclared identifier 'count'` -- a MISSING GLOBAL reported as a
// type error. The two codes feed different statistics ("malformed input"
// against "coverage gap"), so the corpus's failure-cause distribution counted
// those three as broken input rather than as the one gap they share. That
// distribution is the output the corpus exists to produce, which is why a
// wrong code is a defect here and not a cosmetic issue.
//
// The decomposition lives in DecomposeGlobalsPass and not in this frontend,
// per invariant 8: a frontend's product is HIR, and an encoding chosen in the
// frontend is an encoding chosen in twenty-four places instead of one. What
// this file pins is the frontend's half -- which shape each spelling reaches,
// what is refused, and the recorded choice -- plus the decomposition's
// structure. Its MEANING is pinned by solving, in
// test/python/test_mzn_count_verdicts.py: `(+ (ite ...) (ite ...))` has the
// right shape whether the indicators compare against the sought value or
// against each other, and only a solver separates those.

#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation mzn(const std::string& source, const std::string& profile = "default") {
    Lang::SourceUnit unit;
    unit.inline_source = source;
    unit.display_name = "<count-test>";
    TranslateOptions options;
    options.language_id = "minizinc";
    options.profile_id = profile;
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& fragment) {
    return text.find(fragment) != std::string::npos;
}

std::string firstError(const Translation& translation) {
    for (const Diagnostic& diagnostic : translation.diagnostics().all()) {
        if (diagnostic.severity == Severity::ERROR) { return diagnostic.message; }
    }
    return "<no error>";
}

/** How many times @p fragment occurs. `+` is commutative and the builders
 *  canonicalize operand order, so the indicator terms may be emitted in any
 *  sequence -- count them rather than pinning their order (the engine lesson
 *  recorded on 2026-09-19). */
std::size_t occurrences(const std::string& text, const std::string& fragment) {
    std::size_t n = 0;
    for (std::size_t at = text.find(fragment); at != std::string::npos;
         at = text.find(fragment, at + 1)) {
        ++n;
    }
    return n;
}

const char* kDecls =
    "array[1..3] of var 0..9: x;\n"
    "var int: c;\n";

} // namespace

int main() {
    std::cout << "======= MiniZinc: the count global =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // A comprehension reaches the global's LIST shape: there is no array
        // to point at, because the terms are computed. One indicator per term,
        // and all three present -- a dropped term is a different count with
        // the same shape.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint count([x[i] | i in 1..3], 0, c);\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(occurrences(smt, "(ite (= 0 (select x") == 3
               || occurrences(smt, "(ite (= (select x") == 3);
        VERIFY(!has(smt, "count"));   // the GLOBAL must not survive the pass
    }

    {
        // A declared array reaches the INDEXED shape, with the bounds the
        // declaration gave. Same decomposition, so the same three indicators.
        const Translation translation = mzn(
            std::string(kDecls) + "constraint count(x, 5, c);\n"
                                  "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(occurrences(smt, "(ite (= 5 (select x") == 3
               || occurrences(smt, "(ite (= (select x") == 3);
    }

    {
        // A parameter array's cells are values, so they fold: the indicators
        // are over literals and the builders collapse them. What must NOT
        // happen is a surviving GLOBAL or a select into an array that was
        // never declared.
        const Translation translation = mzn(
            "array[1..4] of int: w = [0, 3, 0, 7];\n"
            "var int: c;\n"
            "constraint count(w, 0, c);\n"
            "constraint c = 2;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(!has(smt, "count"));
        VERIFY(!has(smt, "select w"));
    }

    {
        // The recorded EncodingChoice. There is one encoding, so the strategy
        // is named for what was built rather than for the profile's style --
        // reporting "quantified" under the quantified profile would describe
        // an encoding nobody wrote.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint count([x[i] | i in 1..3], 0, c);\n"
              "solve satisfy;\n",
            "quantified");
        VERIFY(translation.ok());
        bool found = false;
        for (const EncodingChoice& choice : translation.report().choices()) {
            if (choice.unified_op == "count") {
                VERIFY(choice.strategy == "count-indicator-sum");
                VERIFY(choice.fidelity.sound && choice.fidelity.complete && choice.fidelity.preserves_optimum && choice.fidelity.bounds.empty() && choice.fidelity.count_status == CountStatus::UNASSESSED);
                found = true;
            }
        }
        VERIFY(found);
    }

    {
        // An empty comprehension is `c = 0`, not an error: a generator that
        // happens to be empty is a legal model, and `mkOp(ADD, {})` would
        // throw.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint count([x[i] | i in 1..0], 0, c);\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(= c 0)") || has(smt, "(= 0 c)"));
    }

    {
        // A first argument that is neither an array nor a list is a coverage
        // gap named by construct -- E_UNSUPPORTED_CONSTRUCT, not the E_TYPE
        // that `count` itself produced before it existed.
        const Translation translation = mzn(
            std::string(kDecls) + "constraint count(7, 0, c);\n"
                                  "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        VERIFY(has(firstError(translation), "count"));
    }

    {
        // Terms and the sought value must share a sort. A mix would decompose
        // to equalities that are legal in SMT-LIB and are not what the model
        // said -- the trap alldifferent's list shape guards against too.
        const Translation translation = mzn(
            "array[1..2] of var bool: b;\n"
            "var int: c;\n"
            "constraint count([b[1], b[2]], 0, c);\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    std::cout << "All MiniZinc count tests passed.\n";
    return 0;
}
