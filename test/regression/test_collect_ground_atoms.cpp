// collectGroundAtoms silently dropped every atom under a disjunction and
// under a negation.
//
// The walker runs on the NNF of its input, and toNNF leaves exactly four
// shapes above a leaf: AND, OR, NOT, and quantified subformulas. The
// recursion handled AND and stopped there, so
//
//     (or (> x 3) (< y 1))        collected ZERO atoms
//     (not (> x 3))               collected ZERO atoms
//
// -- an empty result for a formula whose atoms are the whole point of the
// function (its only caller is the Python `collect_ground_atoms`, used to
// drive an external CNF abstraction). This is the project's signature
// failure class: a correct-looking traversal whose input makes it always
// skip. OR and NOT now recurse; quantifiers and Boolean constants/variables
// remain deliberate leaves, documented at the site.

#include <iostream>
#include <string>
#include <unordered_set>

#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

using namespace SOMTParser;

namespace {

std::unordered_set<std::shared_ptr<DAGNode>> groundAtomsOf(ParserPtr& p, const std::string& script) {
    if (!p->parseStr(script)) {
        std::cout << "  failed to parse: " << script << "\n";
        VERIFY(false);
    }
    std::unordered_set<std::shared_ptr<DAGNode>> atoms;
    p->collectGroundAtoms(p->getAssertions(), atoms);
    return atoms;
}

bool anyTextContains(const std::unordered_set<std::shared_ptr<DAGNode>>& atoms,
                     ParserPtr& p, const std::string& needle) {
    for (const auto& a : atoms) {
        if (p->toString(a).find(needle) != std::string::npos) return true;
    }
    return false;
}

const char* kDecl =
    "(set-logic ALL)\n"
    "(declare-const x Int)\n"
    "(declare-const y Int)\n"
    "(declare-const b Bool)\n";

} // namespace

int main() {
    std::cout << "======= collectGroundAtoms traversal =======\n";

    // ---- Atoms under a disjunction are collected. --------------------------
    {
        ParserPtr p = newParser();
        auto atoms = groundAtomsOf(p, std::string(kDecl) +
            "(assert (or (> x 3) (< y 1)))\n(check-sat)\n");
        VERIFY(anyTextContains(atoms, p, ">") || anyTextContains(atoms, p, "<"));
        // Both disjuncts, not just one of them.
        bool sawGt = false, sawLt = false;
        for (const auto& a : atoms) {
            const std::string s = p->toString(a);
            if (s.find(">") != std::string::npos) sawGt = true;
            if (s.find("<") != std::string::npos) sawLt = true;
        }
        VERIFY(sawGt && sawLt);
    }

    // ---- An atom under a negation is collected. ----------------------------
    {
        // A negated UF predicate: the parser normalises a negated COMPARISON
        // to its dual at parse time ((not (> x 3)) becomes (<= x 3)), which
        // would exercise nothing -- a UF application stays under the NOT.
        ParserPtr p = newParser();
        auto atoms = groundAtomsOf(p,
            "(set-logic ALL)\n"
            "(declare-fun p (Int) Bool)\n"
            "(declare-const x Int)\n"
            "(assert (not (p x)))\n(check-sat)\n");
        VERIFY(atoms.size() == 1);
        VERIFY(anyTextContains(atoms, p, "p"));
    }

    // ---- Mixed conjunction/disjunction/negation. ---------------------------
    {
        ParserPtr p = newParser();
        auto atoms = groundAtomsOf(p, std::string(kDecl) +
            "(assert (and (or (> x 3) (not (< y 1))) (>= x y)))\n(check-sat)\n");
        VERIFY(atoms.size() == 3);
    }

    // ---- Boolean variables and constants are leaves, not atoms. ------------
    {
        ParserPtr p = newParser();
        auto atoms = groundAtomsOf(p, std::string(kDecl) +
            "(assert (or b (not b)))\n(check-sat)\n");
        VERIFY(atoms.empty());
    }

    // ---- Implication is eliminated by the NNF, not skipped. -----------------
    {
        ParserPtr p = newParser();
        auto atoms = groundAtomsOf(p, std::string(kDecl) +
            "(assert (=> b (> x 3)))\n(check-sat)\n");
        VERIFY(atoms.size() == 1);
        VERIFY(anyTextContains(atoms, p, ">"));
    }

    std::cout << "All collectGroundAtoms tests passed." << std::endl;
    return 0;
}
