#define SOMT_LTLF_CORE_TEST_ONLY
#include "../../languages/syntcomp/src/syntcomp.cpp"

#include "test_helpers.h"
#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <vector>

using namespace SOMTParser::Lang;
using Letter = std::set<std::string>;

static bool evalBdd(BddManager::Id id, const BddManager& bdds, const Letter& letter) {
    while (id > 1) {
        const auto node = bdds.get(id);
        id = letter.count(bdds.variableName(node.variable)) ? node.high : node.low;
    }
    return id == 1;
}

static std::size_t step(const SymbolicAutomaton& automaton, const BddManager& bdds,
                        std::size_t state, const Letter& letter) {
    std::size_t selected = automaton.states.size();
    for (const auto& [target, condition] : automaton.edges[state]) {
        if (evalBdd(condition, bdds, letter)) {
            VERIFY(selected == automaton.states.size());
            selected = target;
        }
    }
    VERIFY(selected < automaton.states.size());
    return selected;
}

static bool evaluate(const FormulaPtr& formula, const std::vector<Letter>& word,
                     std::size_t at, std::size_t prefix) {
    switch (formula->kind) {
    case Formula::TRUE_VALUE: return true;
    case Formula::FALSE_VALUE: return false;
    case Formula::VARIABLE: return word[at].count(formula->variable) != 0;
    case Formula::NOT: return !evaluate(formula->left, word, at, prefix);
    case Formula::AND:
        return evaluate(formula->left, word, at, prefix)
            && evaluate(formula->right, word, at, prefix);
    case Formula::OR:
        return evaluate(formula->left, word, at, prefix)
            || evaluate(formula->right, word, at, prefix);
    case Formula::NEXT_WEAK:
        return evaluate(formula->left, word, at+1 == word.size() ? prefix : at+1, prefix);
    default: VERIFY(false); return false;
    }
}

static bool globally(const FormulaPtr& body, const std::vector<Letter>& word,
                     std::size_t prefix) {
    for (std::size_t at = 0; at < word.size(); ++at) {
        if (!evaluate(body, word, at, prefix)) { return false; }
    }
    return true;
}

static bool accepts(const SymbolicAutomaton& automaton, const BddManager& bdds,
                    const std::vector<Letter>& word, std::size_t prefix) {
    std::size_t state = automaton.initial;
    for (std::size_t at = 0; at < prefix; ++at) { state = step(automaton, bdds, state, word[at]); }
    std::map<std::pair<std::size_t,std::size_t>,std::size_t> seen;
    std::vector<bool> accepting;
    std::size_t at = prefix;
    for (;;) {
        const auto key = std::make_pair(state, at);
        const auto found = seen.find(key);
        if (found != seen.end()) {
            for (std::size_t q = found->second; q < accepting.size(); ++q) {
                if (accepting[q]) { return true; }
            }
            return false;
        }
        seen.emplace(key, accepting.size());
        accepting.push_back(automaton.states[state].accepting);
        state = step(automaton, bdds, state, word[at]);
        at = at+1 == word.size() ? prefix : at+1;
    }
}

int main() {
    FormulaFactory f;
    const auto i = f.atom("i");
    const auto o = f.atom("o");
    const auto yes = f.boolean(true);
    const auto no = f.boolean(false);
    const std::vector<std::tuple<FormulaPtr,FormulaPtr,FormulaPtr,FormulaPtr>> examples{
        {yes, yes, yes, f.make(Formula::IFF, i, f.make(Formula::NEXT_WEAK, o))},
        {i, o, f.make(Formula::IMPLIES, o, f.make(Formula::NEXT_WEAK, i)),
               f.make(Formula::IFF, o, f.make(Formula::NEXT_WEAK, i))},
        {yes, o, o, no}, // guarantee fails before a later assumption failure
        {yes, no, no, no}, // assumption failure cannot rescue PRESET
        {no, no, yes, no},
    };
    std::size_t checked = 0;
    for (const auto& [initial, preset, a, b] : examples) {
        BddManager bdds({"i", "o"});
        InfiniteSafetyMonitor monitor(f, bdds);
        const auto automaton = monitor.automaton(initial, preset,
            f.make(Formula::GLOBALLY, a), f.make(Formula::GLOBALLY, b));
        for (std::size_t prefix = 0; prefix <= 2; ++prefix) {
            for (std::size_t cycle = 1; cycle <= 2; ++cycle) {
                const std::size_t length = prefix+cycle;
                std::size_t count = 1;
                for (std::size_t at = 0; at < length; ++at) { count *= 4; }
                for (std::size_t value = 0; value < count; ++value) {
                    std::vector<Letter> word(length);
                    std::size_t digits = value;
                    for (auto& letter : word) {
                        if (digits & 1U) { letter.insert("i"); }
                        if (digits & 2U) { letter.insert("o"); }
                        digits /= 4;
                    }
                    const bool expected = !evaluate(initial, word, 0, prefix)
                        || (evaluate(preset, word, 0, prefix)
                            && (!globally(a, word, prefix) || globally(b, word, prefix)));
                    VERIFY(accepts(automaton, bdds, word, prefix) == expected);
                    ++checked;
                }
            }
        }
        for (std::size_t q = 0; q < automaton.states.size(); ++q) {
            for (const auto& letter : std::vector<Letter>{{},{"i"},{"o"},{"i","o"}}) {
                (void)step(automaton, bdds, q, letter);
            }
        }
    }
    std::cout << "infinite_safety_lassos=" << checked << " PASS\n";
}
