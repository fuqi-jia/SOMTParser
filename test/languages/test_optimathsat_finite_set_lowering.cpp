#include "somtparser/lowering/z3_finite_set_lowering.h"
#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <stdexcept>
#include <string>

using namespace SOMTParser;

namespace {
void checkReadable(const std::string& text) {
    VERIFY(text.find("((_ map ") == std::string::npos);
    VERIFY(text.find("set.inter") == std::string::npos);
    VERIFY(text.find("set.union") == std::string::npos);
    VERIFY(text.find("set.minus") == std::string::npos);
    auto parser=newParser();
    VERIFY(parser->parseStr(text));
}

void testFiniteIntersectionAndCardinality() {
    // Array-valued sets reproduce the MiniZinc gt-sort construction without
    // depending on a particular corpus ID or on a fixed carrier size.
    const auto output=Lower::lowerFiniteSetsForOptiMathSat(
        "(set-logic ALL)(declare-const x (Array Int (Set Int)))"
        "(assert (= (select x 0) (set.inter (select x 0)"
        " (set.insert (- 2) 0 3 (as set.empty (Set Int))))))"
        "(assert (= (set.card (select x 0)) 2))(check-sat)");
    checkReadable(output);
    VERIFY(output.find("set.card")==std::string::npos);
    VERIFY(output.find("(Array Int (Array Int Bool))")!=std::string::npos);
    VERIFY(output.find("(select __somt_oms_set_operand_")!=std::string::npos);
}

void testSymbolicCandidatesAndLocalSupport() {
    const auto output=Lower::lowerFiniteSetsForOptiMathSat(
        "(declare-const x Int)(declare-const y Int)"
        "(assert (let ((S (set.insert x y (as set.empty (Set Int)))))"
        " (= (set.card (set.minus (set.union S (set.singleton x)) (set.singleton y))) 1)))"
        "(check-sat)");
    checkReadable(output);
    VERIFY(output.find("set.card")==std::string::npos);
    VERIFY(output.find("__somt_z3_set_support_")!=std::string::npos);
}

void testConditionalFactsAndIncrementalContextsDoNotProveSupport() {
    for(const auto& source : {
        "(declare-const S (Set Int))(assert (not (= S (set.singleton 0))))"
        "(assert (= (set.union S (set.singleton 1)) S))",
        "(declare-const S (Set Int))(push 1)(assert (= S (set.singleton 0)))"
        "(pop 1)(assert (= (set.union S (set.singleton 1)) S))",
        "(declare-const S (Set Int))(assert (= S (set.singleton 0)))"
        "(assert (forall ((S (Set Int))) (= (set.union S (set.singleton 1)) S)))"
    }) {
        bool refused=false;
        try { Lower::lowerFiniteSetsForOptiMathSat(source); }
        catch(const std::runtime_error&) { refused=true; }
        VERIFY(refused);
    }
    // A syntactically finite intersection remains valid under negation: its
    // support is intrinsic, rather than inferred from the surrounding formula.
    checkReadable(Lower::lowerFiniteSetsForOptiMathSat(
        "(declare-const S (Set Int))"
        "(assert (not (= (set.inter S (set.singleton 0)) (set.singleton 0))))"));
}

void testDeepAndBranchingTermsDoNotUseTheNativeStack() {
    constexpr std::size_t depth=12000;
    std::string source="(declare-const p Bool)(declare-const S (Set Int))(assert ";
    for(std::size_t i=0;i<depth;++i) source+="(not ";
    source+="(and p (= (set.inter S (set.singleton 0)) (set.singleton 0)))";
    source.append(depth,')'); source+=")(check-sat)";
    const auto output=Lower::lowerFiniteSetsForOptiMathSat(source);
    VERIFY(output.find("((_ map ")==std::string::npos);
    // Reader stack-safety is tested independently; this regression exercises
    // both branches and repeated references in the iterative lowering itself.
    VERIFY(output.find("(and p")!=std::string::npos);
}
}

int main() {
    testFiniteIntersectionAndCardinality();
    testSymbolicCandidatesAndLocalSupport();
    testConditionalFactsAndIncrementalContextsDoNotProveSupport();
    testDeepAndBranchingTermsDoNotUseTheNativeStack();
    return 0;
}
