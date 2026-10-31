#define SOMT_LTLF_CORE_TEST_ONLY
#include "../../languages/syntcomp/src/syntcomp.cpp"

#include "test_helpers.h"
#include <cstddef>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>

using namespace SOMTParser::Lang;

static bool evalFinite(const FormulaPtr& f, const std::vector<std::set<std::string>>& word,
                       std::size_t i) {
    const std::size_t last = word.size() - 1;
    switch (f->kind) {
    case Formula::TRUE_VALUE: return true;
    case Formula::FALSE_VALUE: return false;
    case Formula::VARIABLE: return word[i].count(f->variable) != 0;
    case Formula::NOT: return !evalFinite(f->left, word, i);
    case Formula::AND: return evalFinite(f->left, word, i) && evalFinite(f->right, word, i);
    case Formula::OR: return evalFinite(f->left, word, i) || evalFinite(f->right, word, i);
    case Formula::NEXT_WEAK: return i == last || evalFinite(f->left, word, i + 1);
    case Formula::NEXT_STRONG: return i < last && evalFinite(f->left, word, i + 1);
    case Formula::GLOBALLY:
        for (std::size_t j = i; j < word.size(); ++j)
            if (!evalFinite(f->left, word, j)) return false;
        return true;
    case Formula::EVENTUALLY:
        for (std::size_t j = i; j < word.size(); ++j)
            if (evalFinite(f->left, word, j)) return true;
        return false;
    case Formula::UNTIL:
        for (std::size_t j = i; j < word.size(); ++j) {
            if (evalFinite(f->right, word, j)) return true;
            if (!evalFinite(f->left, word, j)) return false;
        }
        return false;
    case Formula::WEAK_UNTIL: {
        const bool until = evalFinite(FormulaPtr(new Formula{0, Formula::UNTIL, {}, f->left, f->right}), word, i);
        const bool globally = evalFinite(FormulaPtr(new Formula{0, Formula::GLOBALLY, {}, f->left}), word, i);
        return until || globally;
    }
    case Formula::RELEASE: {
        FormulaPtr not_left = FormulaPtr(new Formula{0, Formula::NOT, {}, f->left});
        FormulaPtr not_right = FormulaPtr(new Formula{0, Formula::NOT, {}, f->right});
        FormulaPtr until(new Formula{0, Formula::UNTIL, {}, not_left, not_right});
        FormulaPtr neg(new Formula{0, Formula::NOT, {}, until});
        return evalFinite(neg, word, i);
    }
    case Formula::IMPLIES:
    case Formula::IFF: VERIFY(false); return false;
    }
    VERIFY(false); return false;
}

static bool evalBdd(BddManager::Id id, const BddManager& bdds,
                    const std::set<std::string>& letter) {
    while (id > 1) {
        const auto node = bdds.get(id);
        id = letter.count(bdds.variableName(node.variable)) ? node.high : node.low;
    }
    return id == 1;
}

int main() {
    FormulaFactory f;
    const auto p = f.atom("p");
    const auto q = f.atom("q");
    const auto r = f.atom("r");
    const auto boolean_quotient = f.make(
        Formula::OR,
        f.make(Formula::AND, p, q),
        f.make(Formula::AND, p, f.make(Formula::NOT, q)));
    VERIFY(boolean_quotient->id == p->id);
    const auto temporal_atom = f.make(Formula::GLOBALLY, p);
    const auto temporal_quotient = f.make(
        Formula::OR,
        f.make(Formula::AND, temporal_atom, f.make(Formula::EVENTUALLY, q)),
        f.make(Formula::AND, temporal_atom,
               f.make(Formula::NOT, f.make(Formula::EVENTUALLY, q))));
    VERIFY(temporal_quotient->id == temporal_atom->id);
    const auto implication = f.make(Formula::IMPLIES, p,
                                    f.make(Formula::NEXT_STRONG, q));
    const auto response = f.make(Formula::EVENTUALLY,
                                 f.make(Formula::UNTIL, r, p));
    const auto source = f.make(Formula::AND,
                               f.make(Formula::GLOBALLY, implication), response);
    BddManager bdds({"p", "q", "r"});
    LtlProgression progression(f, bdds);
    const auto dfa = progression.automaton(source->id);
    std::size_t words_checked = 0;
    for (std::size_t length = 1; length <= 4; ++length) {
        std::size_t total = 1;
        for (std::size_t i = 0; i < length; ++i) total *= 8;
        for (std::size_t encoded = 0; encoded < total; ++encoded) {
            std::size_t digits = encoded;
            std::vector<std::set<std::string>> word(length);
            for (std::size_t i = 0; i < length; ++i) {
                const unsigned letter = static_cast<unsigned>(digits % 8);
                digits /= 8;
                if (letter & 1U) word[i].insert("p");
                if (letter & 2U) word[i].insert("q");
                if (letter & 4U) word[i].insert("r");
            }
            std::size_t state = dfa.initial;
            for (const auto& letter : word) {
                std::size_t selected = dfa.states.size();
                for (const auto& [target, condition] : dfa.edges[state]) {
                    if (evalBdd(condition, bdds, letter)) {
                        VERIFY(selected == dfa.states.size());
                        selected = target;
                    }
                }
                VERIFY(selected != dfa.states.size());
                state = selected;
            }
            VERIFY(dfa.states[state].accepting == evalFinite(source, word, 0));
            ++words_checked;
        }
    }
    std::cout << "states=" << dfa.states.size() << " bdd_nodes=" << bdds.size()
              << " exhaustive_words=" << words_checked << " PASS\n";

    const std::vector<FormulaPtr> nested_temporal{
        f.make(Formula::GLOBALLY, f.make(Formula::EVENTUALLY, p)),
        f.make(Formula::EVENTUALLY, f.make(Formula::GLOBALLY, p)),
        f.make(Formula::GLOBALLY,
               f.make(Formula::IMPLIES, f.make(Formula::EVENTUALLY, p),
                      f.make(Formula::UNTIL, q, p))),
        f.make(Formula::UNTIL, p,
               f.make(Formula::RELEASE, q, f.make(Formula::EVENTUALLY, p))),
        f.make(Formula::WEAK_UNTIL,
               f.make(Formula::GLOBALLY, p),
               f.make(Formula::RELEASE, q, f.make(Formula::NEXT_STRONG, r)))
    };
    std::size_t nested_words_checked = 0;
    for (const FormulaPtr& formula : nested_temporal) {
        BddManager formula_bdds({"p", "q", "r"});
        LtlProgression formula_progression(f, formula_bdds);
        const auto formula_dfa = formula_progression.automaton(formula->id);
        for (std::size_t length = 1; length <= 3; ++length) {
            for (std::size_t encoded = 0; encoded < (std::size_t{8} << (3 * (length - 1)));
                 ++encoded) {
                std::size_t digits = encoded;
                std::vector<std::set<std::string>> word(length);
                for (std::size_t i = 0; i < length; ++i) {
                    const unsigned letter = static_cast<unsigned>(digits % 8);
                    digits /= 8;
                    if (letter & 1U) { word[i].insert("p"); }
                    if (letter & 2U) { word[i].insert("q"); }
                    if (letter & 4U) { word[i].insert("r"); }
                }
                std::size_t state = formula_dfa.initial;
                for (const auto& letter : word) {
                    std::size_t selected = formula_dfa.states.size();
                    for (const auto& [target, condition] : formula_dfa.edges[state]) {
                        if (evalBdd(condition, formula_bdds, letter)) {
                            VERIFY(selected == formula_dfa.states.size());
                            selected = target;
                        }
                    }
                    VERIFY(selected != formula_dfa.states.size());
                    state = selected;
                }
                VERIFY(formula_dfa.states[state].accepting
                       == evalFinite(formula, word, 0));
                ++nested_words_checked;
            }
        }
    }
    std::cout << "nested_temporal_states=" << nested_temporal.size()
              << " exhaustive_words=" << nested_words_checked
              << " finite_boolean_quotient PASS\n";

    FormulaFactory next_formulas;
    const FormulaPtr weak_next = next_formulas.make(
        Formula::NEXT_WEAK, next_formulas.boolean(true));
    const FormulaPtr strong_next = next_formulas.make(
        Formula::NEXT_STRONG, next_formulas.boolean(true));
    BddManager next_bdds({"i"});
    LtlProgression next_progression(next_formulas, next_bdds);
    const auto weak_dfa = next_progression.automaton(weak_next->id);
    const auto strong_dfa = next_progression.automaton(strong_next->id);
    VERIFY(!weak_dfa.states[weak_dfa.initial].accepting);
    VERIFY(!strong_dfa.states[strong_dfa.initial].accepting);
    for (const auto& letter : {std::set<std::string>{}, std::set<std::string>{"i"}}) {
        const auto advance = [&](const SymbolicAutomaton& automaton,
                                 std::size_t state) {
            for (const auto& [target, condition] : automaton.edges[state]) {
                if (evalBdd(condition, next_bdds, letter)) { return target; }
            }
            VERIFY(false);
            return std::size_t{0};
        };
        const std::size_t weak_after_one = advance(weak_dfa, weak_dfa.initial);
        const std::size_t strong_after_one = advance(strong_dfa, strong_dfa.initial);
        VERIFY(weak_dfa.states[weak_after_one].accepting);
        VERIFY(!strong_dfa.states[strong_after_one].accepting);
        const std::size_t strong_after_two = advance(strong_dfa, strong_after_one);
        VERIFY(strong_dfa.states[strong_after_two].accepting);
    }
    std::cout << "weak-next accepts one position; strong-next accepts from two positions PASS\n";

    std::ifstream input("languages/syntcomp/instances/ok/syft_2_068.tlsf",
                        std::ios::binary);
    VERIFY(input.good());
    const std::string tlsf((std::istreambuf_iterator<char>(input)),
                           std::istreambuf_iterator<char>());
    const std::size_t section = tlsf.find("GUARANTEES");
    VERIFY(section != std::string::npos);
    const std::size_t open = tlsf.find('{', section);
    VERIFY(open != std::string::npos);
    unsigned depth = 1;
    std::size_t close = open + 1;
    for (; close < tlsf.size() && depth != 0; ++close) {
        if (tlsf[close] == '{') { ++depth; }
        else if (tlsf[close] == '}') { --depth; }
    }
    VERIFY(depth == 0);
    std::string formula_text = tlsf.substr(open + 1, close - open - 2);
    const std::size_t last = formula_text.find_last_not_of(" \t\r\n");
    if (last != std::string::npos && formula_text[last] == ';') {
        formula_text.erase(last);
    }
    Lexer lexer(formula_text);
    std::vector<Token> tokens;
    std::string error;
    VERIFY(lexer.read(tokens, error));
    const std::set<std::string> signals{
        "p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8", "p9", "p10"};
    FormulaFactory official_formulas;
    SOMTParser::Uir::Diagnostics diagnostics;
    FormulaParser parser(std::move(tokens), signals, official_formulas);
    const FormulaPtr official = parser.parse(diagnostics);
    for (const auto& diagnostic : diagnostics.all()) {
        std::cerr << diagnostic.message << '\n';
    }
    VERIFY(official && !diagnostics.hasErrors());
    std::vector<std::string> official_atoms(signals.begin(), signals.end());
    BddManager official_bdds(official_atoms);
    LtlProgression official_progression(official_formulas, official_bdds);
    const auto official_dfa = official_progression.automaton(official->id);
    std::cout << "official_syft_2_068 formula_states=" << official_dfa.states.size()
              << " bdd_nodes=" << official_bdds.size() << " C++ parser PASS\n";
}
