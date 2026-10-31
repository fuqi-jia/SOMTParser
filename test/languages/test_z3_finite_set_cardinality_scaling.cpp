// Focused regression candidate for test/languages. No timing threshold: these
// assertions cover output shape and exact symbolic duplicate handling.
#include "somtparser/lowering/z3_finite_set_lowering.h"
#include "test_helpers.h"

#include <cstddef>
#include <string>
#include <string_view>

using namespace SOMTParser;

namespace {
std::string lower(const std::string& source) {
    return Lower::lowerFiniteSetsForZ3(source);
}

std::size_t occurrences(std::string_view text, std::string_view needle) {
    std::size_t count = 0;
    for (std::size_t at = 0; (at = text.find(needle, at)) != std::string_view::npos;
         at += needle.size()) {
        ++count;
    }
    return count;
}

void testConcreteCarrierHasNoPairwiseGuardsAndSharesSetTerm() {
    const auto text = lower(R"SMT((set-logic ALL)
(declare-const S (Set Int))
(assert (forall ((u Int))
  (=> (set.member u S) (and (<= 0 u) (<= u 7)))) )
(assert (= (set.card (set.union S (as set.empty (Set Int)))) 8))
(check-sat)
)SMT");
    VERIFY(text.find("set.card") == std::string::npos);
    VERIFY(text.find("(not (= ") == std::string::npos);
    VERIFY(occurrences(text, "((_ map or) S") == 1);
    VERIFY(text.find("__somt_z3_set_card_set_0") != std::string::npos);
}

void testMixedSupportGuardsOnlySymbolAgainstUniquePriorSupport() {
    const auto text = lower(R"SMT((set-logic ALL)
(declare-const S (Set Int))
(declare-const x Int)
(assert (forall ((u Int))
  (=> (set.member u S) (and (<= 0 u) (<= u 7)))) )
(assert (= (set.card (set.union S (set.singleton x))) 9))
(check-sat)
)SMT");
    VERIFY(text.find("set.card") == std::string::npos);
    VERIFY(occurrences(text, "(not (= x ") == 8);
    VERIFY(text.find("(not (= 1 0))") == std::string::npos);
    VERIFY(occurrences(text, "((_ map or) S") == 1);
}

void testExactDuplicateSymbolicCandidateIsRemoved() {
    const auto text = lower(
        "(declare-const x Int)(declare-const y Int)"
        "(assert (= (set.card (set.union (set.singleton x)"
        "(set.singleton y) (set.singleton x))) 2))(check-sat)");
    VERIFY(text.find("set.card") == std::string::npos);
    VERIFY(occurrences(text, "(not (= y x))") == 1);
    VERIFY(text.find("(not (= x x))") == std::string::npos);
}

void testGeneratedSetBindingCannotCaptureInputName() {
    const auto text = lower(
        "(declare-const __somt_z3_set_card_set_0 Int)"
        "(assert (= (set.card (set.union (set.singleton (- 1))"
        "(set.singleton 0))) 2))(check-sat)");
    VERIFY(text.find("(__somt_z3_set_card_set_1 ") != std::string::npos);
}
} // namespace

int main() {
    testConcreteCarrierHasNoPairwiseGuardsAndSharesSetTerm();
    testMixedSupportGuardsOnlySymbolAgainstUniquePriorSupport();
    testExactDuplicateSymbolicCandidateIsRemoved();
    testGeneratedSetBindingCannotCaptureInputName();
    return 0;
}
