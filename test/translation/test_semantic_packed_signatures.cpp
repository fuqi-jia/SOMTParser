#include "somtparser/translation/semantics.h"

#include "test_helpers.h"

#include <algorithm>
#include <iostream>
#include <string>
#include <utility>

using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;
namespace S = SOMTParser::Uir::Sem;

namespace {

bool composes(const H::ConstraintModel& first, const H::ConstraintModel& second) {
    auto frontend = S::directLanguageToRelationalContract(first, "wcnf", Fidelity::exact());
    auto backend = S::relationalToSmtContract(second, false);
    Diagnostics diagnostics;
    // Each stage is valid by itself. The regression concerns their shared
    // interface, not a malformed individual contract.
    VERIFY(frontend.validate(diagnostics));
    VERIFY(backend.validate(diagnostics));
    S::TranslationPipeline pipeline;
    pipeline.add(std::move(frontend));
    pipeline.add(std::move(backend));
    return pipeline.validate(diagnostics);
}

} // namespace

int main() {
    H::ConstraintModel original;
    // A billion names must remain a pair of range descriptors even during
    // compatibility checks. No variable or assignment is materialized here.
    original.bool_var_ranges.push_back({"x", 1, 1000000000ULL});
    original.bool_var_ranges.push_back({"y", 7, 4});
    VERIFY(composes(original, original));

    auto reordered = original;
    std::reverse(reordered.bool_var_ranges.begin(), reordered.bool_var_ranges.end());
    VERIFY(composes(original, reordered));

    auto different = original;
    different.bool_var_ranges[0].prefix = "z";
    VERIFY(!composes(original, different));

    different = original;
    ++different.bool_var_ranges[0].first;
    VERIFY(!composes(original, different));

    different = original;
    --different.bool_var_ranges[0].count;
    VERIFY(!composes(original, different));

    different = original;
    different.bool_var_ranges[0].sort = H::Sort::integer();
    VERIFY(!composes(original, different));

    different = original;
    different.bool_var_ranges.pop_back();
    VERIFY(!composes(original, different));
    VERIFY(!composes(original, H::ConstraintModel{}));
    VERIFY(!composes(H::ConstraintModel{}, original));

    std::cout << "Packed signature composition rejects incompatible interfaces.\n";
}
