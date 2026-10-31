// Semantic-contract validation must not grow quadratically with the signature.
//
// Two nested loops in the semantic-contract stage were quadratic in the
// number of declared symbols, which for a direct frontend is the number of
// declared variables:
//
//   * `TranslationContract::validate` called `symbolsNamed` four times for
//     every entry of `symbol_map` -- twice itself and twice inside
//     `namedSymbolsMap` -- and each call scanned the whole signature.
//   * `sameSignature` compared every symbol on one side against every symbol
//     on the other, although its first test is a name inequality, so a pair
//     with different names could never have matched.
//
// Neither was visible on any fixture in the tree, because a fixture is small.
// It took a vendored corpus with 190 KB instances to make it a wall-clock
// problem: the contract stage alone was 8.9 seconds on 16000 clauses against
// 51 milliseconds on 1000, a 175x rise for a 16x input, while parsing, type
// checking, the passes and lowering all stayed close to linear.
//
// This test is a RATIO rather than an absolute bound on purpose. An absolute
// millisecond figure is a statement about the machine, and would have to be
// loose enough on a slow one to pass on a fast one even when quadratic. The
// ratio between two sizes helps distinguish the algorithms. Time validation
// of complete translated contracts separately from parsing and lowering: those
// stages cannot hide or cause a regression in either signature lookup. Measure
// process CPU time, since scheduling delays need not scale with the input.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <algorithm>
#include <array>
#include <chrono>
#include <ctime>
#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

/** A CNF with @p clauses three-literal clauses over @p clauses/4 variables.
 *  Deterministic: a fixed recurrence rather than a random engine, so a slow
 *  run can be reproduced exactly. */
std::string cnf(std::size_t clauses) {
    const std::size_t vars = clauses / 4 + 2;
    std::string out = "p cnf " + std::to_string(vars) + " "
                    + std::to_string(clauses) + "\n";
    std::size_t state = 12345;
    for (std::size_t i = 0; i < clauses; ++i) {
        for (int k = 0; k < 3; ++k) {
            state = state * 1103515245 + 12345;
            const std::size_t v = 1 + (state >> 16) % vars;
            if ((state >> 8) & 1u) { out += '-'; }
            out += std::to_string(v);
            out += ' ';
        }
        out += "0\n";
    }
    return out;
}

struct Timing {
    double cpu_ms;
    double wall_ms;
};

Translation translateCnf(const std::string& text) {
    Lang::SourceUnit unit;
    unit.inline_source = text;
    unit.display_name = "scaling.cnf";
    TranslateOptions opts;
    opts.language_id = "dimacs";
    opts.profile_id = "ground";

    auto t = translate(unit, opts);
    VERIFY(t.ok());
    return t;
}

// This optional test-only workload checks that the measurement harness still
// rejects quadratic signature scans. It does not modify production validation
// and is not evidence of reproducing a production regression.
void quadraticSignatureProbe(const Translation& translation) {
    const auto& symbols = translation.semantics().stages().front().target_signature.symbols;
    for (const auto& symbol : symbols) {
        std::size_t matches = 0;
        for (const auto& candidate : symbols) {
            if (symbol.name == candidate.name) { ++matches; }
        }
        VERIFY(matches == 1);
    }
}

Timing validateMs(const Translation& translation, bool quadratic_probe) {
    Uir::Diagnostics diagnostics;
    const auto validate = [&]() {
        VERIFY(translation.semantics().validate(diagnostics));
        if (quadratic_probe) { quadraticSignatureProbe(translation); }
    };
    validate();
    // Five small validations previously covered only 6--10 ms of CPU. A
    // single millisecond of allocation/cache variation can then move a ratio
    // past its threshold. Accumulate at least 100 ms for each size instead;
    // retain the same input sizes and threshold and report all observations.
    const auto started = std::chrono::steady_clock::now();
    const auto cpu_started = std::clock();
    VERIFY(cpu_started != std::clock_t(-1));
    const double minimum_ticks = 0.1 * static_cast<double>(CLOCKS_PER_SEC);
    std::clock_t cpu_finished = cpu_started;
    std::size_t repetitions = 0;
    do {
        validate();
        ++repetitions;
        cpu_finished = std::clock();
        VERIFY(cpu_finished != std::clock_t(-1));
        VERIFY(cpu_finished >= cpu_started);
    } while (static_cast<double>(cpu_finished - cpu_started) < minimum_ticks);
    const auto elapsed = std::chrono::steady_clock::now() - started;
    std::cout << "    " << repetitions << " repetitions, "
              << 1000.0 * static_cast<double>(cpu_finished - cpu_started) / CLOCKS_PER_SEC
              << " ms CPU total\n";
    return {1000.0 * static_cast<double>(cpu_finished - cpu_started) / CLOCKS_PER_SEC / repetitions,
            std::chrono::duration<double, std::milli>(elapsed).count() / repetitions};
}

} // namespace

int main(int argc, char** argv) {
    const bool quadratic_probe = argc == 2 && std::string(argv[1]) == "--quadratic-signature-probe";
    VERIFY(argc == 1 || quadratic_probe);
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    std::cout << "======= semantic validation scales with signature size =======\n";

    const auto small_model = translateCnf(cnf(2000));
    const auto large_model = translateCnf(cnf(32000));
    std::array<double, 7> ratios;
    for (std::size_t sample = 0; sample < ratios.size(); ++sample) {
        Timing small{}, large{};
        if (sample % 2 == 0) {
            small = validateMs(small_model, quadratic_probe);
            large = validateMs(large_model, quadratic_probe);
        } else {
            large = validateMs(large_model, quadratic_probe);
            small = validateMs(small_model, quadratic_probe);
        }
        VERIFY(small.cpu_ms > 0.0);
        ratios[sample] = large.cpu_ms / small.cpu_ms;
        std::cout << "  sample " << sample + 1 << ": 2000 clauses " << small.cpu_ms
                  << " ms CPU, " << small.wall_ms << " ms wall; 32000 clauses "
                  << large.cpu_ms << " ms CPU, " << large.wall_ms
                  << " ms wall; ratio " << ratios[sample] << '\n';
    }
    std::sort(ratios.begin(), ratios.end());
    const double ratio = ratios[ratios.size() / 2];
    std::cout << "  validation CPU ratio: " << ratio << " (median of seven pairs)\n";
    if (quadratic_probe) {
        std::cout << "  TEST-ONLY quadratic signature workload; production validation unchanged\n";
    }

    // SIXTEEN times the input, not four. The first version of this test used
    // 2000 against 8000, and a breakage probe showed it could not fail: with
    // `sameSignature` restored to its quadratic form the ratio moved from
    // 5.1 to only 5.8, because at those sizes the quadratic term was still
    // small beside the linear stages it shares the total with. The defect was
    // real and the test was blind to it.
    //
    // A quadratic term needs room to dominate before a ratio can see it. Over
    // 16x, linear predicts ~16 and the quadratic predicted ~250.
    //
    // The original end-to-end measurements were 18-20 for fixed code, 57
    // with `sameSignature` reverted, and 81 with symbol lookup reverted.
    // Retain its bound of 35 while measuring the stage containing both bugs.
    // A deliberate quadratic-signature probe must still fail this assertion.
    // Wall times remain in the output to make scheduling delays visible.
    VERIFY(ratio < 35.0);

    std::cout << "All semantics scaling tests passed.\n";
    return 0;
}
