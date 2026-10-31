// Tseitin preserves the MODEL COUNT, as a property rather than an assertion.
//
// `Fidelity::preserves_count` is a claim, and a claim that only a boolean
// asserts is one nothing can falsify. This counts instead: enumerate the
// models of a small formula over its own variables by brute force, enumerate
// the models of its Tseitin CNF over ALL variables including auxiliaries, and
// require the two to be equal.
//
// That equality is exactly what two-sided gate clauses buy. `and` emits
// `(¬c ∨ childᵢ)` for each child AND `(¬child₁ ∨ … ∨ ¬childₙ ∨ c)`, so the
// auxiliary is functionally determined by the originals and each source model
// extends to exactly ONE target model. A one-sided (Plaisted-Greenbaum)
// encoding would leave the auxiliary free and multiply the count -- and would
// still be equisatisfiable, which is why satisfiability tests cannot see it.
//
// One formula is not enough to make that last claim testable, though: an
// auxiliary's value can be pinned by something OTHER than its own gate's
// two-sidedness -- namely, by the root being asserted true and forwarded
// through an outer gate that stayed two-sided. Case 1 below turned out to be
// exactly that trap (found by a breakage probe: deleting the `and` gate's
// `(⋀ childᵢ) → c` clause did not move `after` at all). Case 2 is the
// formula that actually needs the direction under test; see its comment.

#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

/** Every assignment over @p names that satisfies @p formula, counted by
 *  brute-force enumeration and the parser's own model evaluator -- so this
 *  measures what the library thinks a model is, not a hand-rolled truth
 *  table. */
std::size_t countModels(Parser& parser,
                        const std::vector<std::string>& names,
                        const std::shared_ptr<DAGNode>& formula) {
    std::size_t models = 0;
    const std::size_t total = std::size_t{1} << names.size();
    for (std::size_t bits = 0; bits < total; ++bits) {
        std::string model_text = "(model";
        for (std::size_t i = 0; i < names.size(); ++i) {
            const bool value = ((bits >> i) & 1u) != 0;
            model_text += " (define-fun " + names[i] + " () Bool "
                        + (value ? "true" : "false") + ")";
        }
        model_text += ")";
        const ModelPtr m = parser.parseModel(model_text);
        const std::shared_ptr<DAGNode> result = parser.evaluate(formula, m);
        if (result && result->isTrue()) { ++models; }
    }
    return models;
}

/** Parse @p script (one assertion), Tseitin-convert it, and require the
 *  brute-force model count over its own declared variables (@p
 *  original_names, pinned against @p expected_before so a bug in
 *  countModels/evaluate cannot pass silently) to equal the brute-force model
 *  count of `clauses ∧ root` over every variable the CNF mentions, auxiliaries
 *  included. That second count is `after` in the two case comments below. */
void checkCountPreserved(const char* script,
                          const std::vector<std::string>& original_names,
                          std::size_t expected_before) {
    Parser source;
    VERIFY(source.parseStr(script));
    VERIFY(source.getAssertions().size() == 1);
    const std::size_t before = countModels(source, original_names, source.getAssertions()[0]);
    VERIFY(before == expected_before);

    std::vector<std::shared_ptr<DAGNode>> clauses;
    Parser target;
    VERIFY(target.parseStr(script));
    const std::shared_ptr<DAGNode> root =
        target.toTseitinCNF(target.getAssertions()[0], clauses);
    VERIFY(root != nullptr);
    VERIFY(!clauses.empty());

    // Every variable the CNF mentions, auxiliaries included: `getVariables()`
    // walks both the declared-variable table and the temp-variable table that
    // `mkTempVar` (what each Tseitin gate calls to name its auxiliary) writes
    // into.
    const std::vector<std::shared_ptr<DAGNode>> all_nodes = target.getVariables();
    std::vector<std::string> all;
    all.reserve(all_nodes.size());
    for (const std::shared_ptr<DAGNode>& v : all_nodes) { all.push_back(v->getName()); }
    VERIFY(all.size() > original_names.size());   // auxiliaries exist, or this proves nothing

    std::vector<std::shared_ptr<DAGNode>> conjuncts = clauses;
    conjuncts.push_back(root);
    const std::shared_ptr<DAGNode> cnf = target.mkAnd(conjuncts);
    const std::size_t after = countModels(target, all, cnf);

    // The property. A one-sided encoding gives `after > before`.
    VERIFY(after == before);
}

} // namespace

int main() {
    std::cout << "======= Tseitin preserves the model count =======\n";

    // Case 1: `(a ∧ b) ∨ (¬a ∧ c)` over three variables. The shape has both
    // an `and` and an `or`, so both gate encodings run at least once, and
    // this is `ite(a, b, c)` in disguise: for a=true it is b (c free), for
    // a=false it is c (b free), so 4 of the 8 assignments satisfy it --
    // (T,T,T) (T,T,F) (F,T,T) (F,F,T).
    //
    // What this case does NOT do is detect a one-sided `and` gate. The root
    // is asserted true, and the outer `or` gate is two-sided, so its
    // `c_or → (c_and1 ∨ c_and2)` clause is present regardless of how the
    // `and` gates were built. On every satisfying assignment here, exactly
    // one of the two `and`-children is already pinned false by its own
    // surviving `c → childᵢ` direction (e.g. a=T forces `c_and2` false,
    // since `c_and2 → ¬a` would be violated), which leaves the `or` clause
    // needing the OTHER `and`-auxiliary true -- and that requirement pins it
    // whether or not that auxiliary's own `(⋀ childᵢ) → c` direction exists.
    // A breakage probe confirmed this directly: deleting that direction from
    // the `and` gate left `after` completely unchanged for this formula.
    checkCountPreserved(
        "(set-logic QF_UF)"
        "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)"
        "(assert (or (and a b) (and (not a) c)))",
        {"a", "b", "c"}, 4);

    // Case 2: `x ∨ (a ∧ b)` over three variables -- THIS is the case that
    // discriminates. Correct count is 5: x=T admits all 4 (a, b) pairs, and
    // x=F needs a=b=T for the one remaining model.
    //
    // The reason it discriminates where case 1 does not: at x=T, a=T, b=T,
    // the root's own requirement (`x ∨ c_and`) is ALREADY satisfied by `x`
    // alone, so nothing forces `c_and` either way. A fully two-sided `and`
    // gate still pins it -- `(a ∧ b) → c_and` fires because a and b are both
    // true, so `c_and` must be T, and that single assignment of the
    // originals extends to exactly one CNF model. Drop that direction and
    // `c_and` becomes free at x=T, a=T, b=T: both `c_and = T` and
    // `c_and = F` satisfy every surviving clause, so that one original
    // model would extend to TWO CNF models, and the brute-force count over
    // {x, a, b, c_and, c_or} would come out to 6 instead of 5. The `and`
    // gate's own two-sidedness is load-bearing here in a way case 1 never
    // exercises, which is exactly why this case belongs beside it rather
    // than instead of it.
    checkCountPreserved(
        "(set-logic QF_UF)"
        "(declare-const x Bool)(declare-const a Bool)(declare-const b Bool)"
        "(assert (or x (and a b)))",
        {"x", "a", "b"}, 5);

    // Case 3: `x ∨ (a → b)`, which is the gate the first two cases do not
    // reach at all. Correct count is 7: only (x=F, a=T, b=F) fails.
    //
    // The implication gate's converse clause was a single
    // `(¬a ∨ ¬b ∨ c)` -- which encodes `(a ∧ b) → c`, a different and
    // strictly weaker formula than `(a → b) → c`. With a false, `a → b`
    // holds and so `c` must be true, but that clause is already satisfied
    // by `¬a` and leaves `c` free. Every such assignment therefore extended
    // to two CNF models instead of one and the count came out 9.
    //
    // It stayed EQUISATISFIABLE throughout, which is why nothing caught it:
    // the root is asserted, so the forward direction still forces the
    // formula to hold. Only counting can see it. The correct converse is
    // one clause per disjunct -- `(a ∨ c)` and `(¬b ∨ c)` -- because a
    // disjunction implies `c` exactly when every disjunct does.
    checkCountPreserved(
        "(set-logic QF_UF)"
        "(declare-const x Bool)(declare-const a Bool)(declare-const b Bool)"
        "(assert (or x (=> a b)))",
        {"x", "a", "b"}, 7);

    // Case 4: the remaining gates, so a future edit to any one of them is
    // measured rather than assumed. `xor`, `=` and `ite` were all correct
    // when the implication defect was found; this is what keeps them so.
    //
    // Each is wrapped in `(or x …)` for the reason case 2 documents: with
    // the gate at the root, the root assertion pins its auxiliary whatever
    // the gate's own converse does, and the test stops discriminating.
    checkCountPreserved(
        "(set-logic QF_UF)"
        "(declare-const x Bool)(declare-const a Bool)(declare-const b Bool)"
        "(assert (or x (xor a b)))",
        {"x", "a", "b"}, 6);
    checkCountPreserved(
        "(set-logic QF_UF)"
        "(declare-const x Bool)(declare-const a Bool)(declare-const b Bool)"
        "(assert (or x (= a b)))",
        {"x", "a", "b"}, 6);
    checkCountPreserved(
        "(set-logic QF_UF)"
        "(declare-const x Bool)(declare-const a Bool)(declare-const b Bool)"
        "(declare-const y Bool)"
        "(assert (or x (ite a b y)))",
        {"x", "a", "b", "y"}, 12);

    std::cout << "All Tseitin model-count tests passed.\n";
    return 0;
}
