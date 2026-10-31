/* -*- Source -*-
 * SyGuS-IF 2.1 bounded grammar-enumeration frontend.
 *
 * A selected candidate is related extensionally to a target function and all
 * declare-var symbols remain universally quantified.  Target SAT therefore
 * projects to a grammar-derived define-fun, while target UNSAT is only a
 * grammar-depth result.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/languages/sygus.h"

#include "somtparser/core/kind.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/parser_to_hir.h"

#include <algorithm>
#include <cctype>
#include <climits>
#include <filesystem>
#include <fstream>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <map>
#include <memory>
#include <limits>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

namespace SOMTParser::Lang {

namespace {

namespace H = Uir::Hir;
namespace S = Uir::Sem;
using Uir::ErrorCode;

constexpr std::size_t CANDIDATE_LIMIT = 5000;
constexpr std::size_t GRAMMAR_CIRCUIT_NODE_LIMIT = 100000;

struct Sexp {
    std::string       atom;
    std::vector<Sexp> list;
    bool quoted_symbol = false;

    bool isAtom() const { return !atom.empty() || quoted_symbol; }
    bool isStringLiteral() const {
        return isAtom() && !quoted_symbol && atom.size() >= 2 && atom.front() == '"'
               && atom.back() == '"';
    }
    bool isQuotedSymbol() const { return isAtom() && quoted_symbol; }
    const std::string& head() const {
        static const std::string empty;
        return list.empty() || !list[0].isAtom() || list[0].isStringLiteral()
            ? empty : list[0].atom;
    }
};

bool legalQuotedSymbolCharacter(unsigned char c) {
    return c != '|' && c != '\\'
        && (c >= 0x20 || c == '\t' || c == '\r' || c == '\n');
}

class SexpReader {
public:
    explicit SexpReader(const std::string& source) : source_(source) {}

    bool readAll(std::vector<Sexp>& result, std::string& error) {
        for (;;) {
            skip();
            if (at_ == source_.size()) { return true; }
            Sexp expression;
            if (!read(expression, error)) { return false; }
            result.push_back(std::move(expression));
        }
    }

private:
    void skip() {
        while (at_ < source_.size()) {
            if (source_[at_] == ';') {
                while (at_ < source_.size() && source_[at_] != '\n') { ++at_; }
            } else if (std::isspace(static_cast<unsigned char>(source_[at_]))) {
                ++at_;
            } else {
                return;
            }
        }
    }

    bool read(Sexp& result, std::string& error) {
        skip();
        if (at_ == source_.size()) {
            error = "unexpected end of input";
            return false;
        }
        if (source_[at_] == '(') {
            ++at_;
            for (;;) {
                skip();
                if (at_ == source_.size()) {
                    error = "unterminated list";
                    return false;
                }
                if (source_[at_] == ')') {
                    ++at_;
                    return true;
                }
                Sexp child;
                if (!read(child, error)) { return false; }
                result.list.push_back(std::move(child));
            }
        }
        if (source_[at_] == '"') {
            const std::size_t begin = at_++;
            while (at_ < source_.size()) {
                if (source_[at_] == '"') {
                    if (at_ + 1 < source_.size() && source_[at_ + 1] == '"') {
                        at_ += 2;
                        continue;
                    }
                    ++at_;
                    result.atom = source_.substr(begin, at_ - begin);
                    return true;
                }
                ++at_;
            }
            error = "unterminated SMT-LIB string literal";
            return false;
        }
        if (source_[at_] == '|') {
            const std::size_t begin = at_++;
            while (at_ < source_.size() && source_[at_] != '|') {
                const unsigned char c = static_cast<unsigned char>(source_[at_]);
                if (!legalQuotedSymbolCharacter(c)) {
                    error = "invalid character in SMT-LIB quoted symbol";
                    return false;
                }
                ++at_;
            }
            if (at_ == source_.size()) {
                error = "unterminated SMT-LIB quoted symbol";
                return false;
            }
            ++at_;
            result.atom = source_.substr(begin + 1, at_ - begin - 2);
            result.quoted_symbol = true;
            return true;
        }
        if (source_[at_] == ')') {
            error = "unexpected right parenthesis";
            return false;
        }
        const std::size_t begin = at_;
        while (at_ < source_.size()
               && !std::isspace(static_cast<unsigned char>(source_[at_]))
               && source_[at_] != '(' && source_[at_] != ')') {
            ++at_;
        }
        result.atom = source_.substr(begin, at_ - begin);
        if (result.atom.empty()) {
            error = "empty token";
            return false;
        }
        return true;
    }

    const std::string& source_;
    std::size_t at_ = 0;
};

std::string printSexp(const Sexp& expression) {
    if (expression.isAtom()) {
        return expression.quoted_symbol ? "|" + expression.atom + "|" : expression.atom;
    }
    std::string result = "(";
    for (std::size_t i = 0; i < expression.list.size(); ++i) {
        if (i != 0) { result += " "; }
        result += printSexp(expression.list[i]);
    }
    return result + ")";
}

bool simpleSymbol(const std::string& symbol) {
    if (symbol.empty() || std::isdigit(static_cast<unsigned char>(symbol[0]))) {
        return false;
    }
    for (unsigned char c : symbol) {
        if (!std::isalnum(c) && std::string("~!@$%^&*_-+=<>.?/").find(c)
                                   == std::string::npos) {
            return false;
        }
    }
    return true;
}

bool canPrintAsSimpleIdentifier(const std::string& symbol);

bool simpleSymbol(const Sexp& symbol) {
    if (!symbol.isAtom()) { return false; }
    if (!symbol.quoted_symbol) { return canPrintAsSimpleIdentifier(symbol.atom); }
    return std::all_of(symbol.atom.begin(), symbol.atom.end(),
                       legalQuotedSymbolCharacter);
}

bool canPrintAsSimpleIdentifier(const std::string& symbol) {
    static const std::set<std::string> reserved{
        "true", "false", "and", "or", "not", "=>", "xor", "=", "distinct",
        "ite", "forall", "exists", "let", "lambda", "match", "par", "as",
        "_", "!"};
    return simpleSymbol(symbol) && reserved.count(symbol) == 0;
}

std::string renderSymbol(const std::string& symbol) {
    return canPrintAsSimpleIdentifier(symbol) ? symbol : "|" + symbol + "|";
}

std::string quoteSmtString(const std::string& value) {
    std::string result;
    result.reserve(value.size() + 2);
    result.push_back('"');
    for (char c : value) {
        // A raw backslash could begin SMT-LIB's Unicode escape syntax in the
        // emitted token. Encode it as the scalar U+005C so the parsed String
        // retains the literal character rather than interpreting its suffix.
        if (c == '\\') {
            result += "\\u{5c}";
        } else {
            result.push_back(c);
            if (c == '"') { result.push_back('"'); }
        }
    }
    result.push_back('"');
    return result;
}

Sexp symbolSexp(std::string value) {
    Sexp result;
    result.atom = std::move(value);
    result.quoted_symbol = !canPrintAsSimpleIdentifier(result.atom);
    return result;
}

bool unsignedDecimal(const std::string& text) {
    return !text.empty() && (text == "0" || text.front() != '0')
           && std::all_of(text.begin(), text.end(), [](unsigned char c) {
                  return std::isdigit(c) != 0;
              });
}

// SyGuS 1.0 admitted signed integer tokens; 2.x writes unary negation.
// Keep arbitrary precision by desugaring the spelling, never parsing to int64.
bool legacyNegativeInteger(const std::string& text) {
    return text.size() > 1 && text.front() == '-'
           && unsignedDecimal(text.substr(1));
}

struct Typed {
    std::string name;
    std::string sort;
    H::Sort     hir_sort;
};

struct Nonterminal {
    std::string       name;
    std::string       sort;
    H::Sort           hir_sort;
    std::vector<Sexp> rules;
};

struct AstGrammarProduction {
    std::string constructor;
    std::vector<std::string> child_nonterminals;
    std::vector<std::string> child_selectors;
    std::vector<std::string> child_markers;
    std::vector<std::string> literal_sorts;
    std::vector<std::string> literal_selectors;
    std::vector<std::string> literal_markers;
    std::vector<unsigned> literal_bit_widths;
    Sexp source_template;
};

struct AstGrammarNonterminal {
    std::string name;
    std::string sort;
    std::string ast_sort;
    std::string eval_name;
    std::string render_name;
    std::vector<AstGrammarProduction> productions;
};

class SygusParser {
    struct SynthFunction {
        std::string name;
        std::vector<Typed> parameters;
        std::string return_sort;
        H::Sort return_hir_sort = H::Sort::boolean();
        bool default_grammar_requested = false;
        bool invariant = false;
        std::size_t command_index = 0;
        Sexp grammar_declarations;
        Sexp grammar_rules;
        std::vector<std::string> candidates;
        std::vector<std::vector<S::ChoiceAlternative::Binding>> bindings;
        std::vector<std::string> selectors;
        bool compact_grammar = false;
        bool empty_bounded_grammar = false;
        std::string compact_smt_body;
        std::vector<std::string> compact_selectors;
        std::vector<S::ChoiceAlternative::Binding> compact_bindings;
        S::GrammarChoiceObservable grammar_choice;
        bool unbounded_ast = false;
        bool unbounded_direct_constant = false;
        std::string ast_root_target;
        std::string witness_text_target;
        std::string witness_value_target;
        std::string unbounded_prelude;
        std::string unbounded_source_term_placeholder;
        std::string unbounded_source_term_symbol;
    };

public:
    SygusParser(std::string source, std::string file, unsigned depth,
                bool unbounded_grammar = false)
        : source_(std::move(source)), file_(std::move(file)), depth_(depth),
          unbounded_grammar_(unbounded_grammar) {}

    H::ConstraintModelPtr parse(Uir::Diagnostics& diagnostics,
                                Uir::TranslationReport& report) {
        std::string error;
        SexpReader reader(source_);
        if (!reader.readAll(commands_, error)) {
            diagnostics.error(ErrorCode::E_PARSE, "SyGuS parse error: " + error);
            return nullptr;
        }
        std::string prefix = "__somt_sygus_";
        while (source_.find(prefix) != std::string::npos) { prefix += "x"; }
        hole_prefix_ = prefix + "constant_";
        while (source_.find(hole_prefix_) != std::string::npos) { hole_prefix_ += "x"; }
        hole_marker_ = prefix + "constant_hole";
        if (!readCommands(diagnostics)) {
            return nullptr;
        }
        initializeTargetHelperNames(prefix);
        if (!computeDefinitionGlobalClosure(diagnostics)) { return nullptr; }
        initializeUniversalAliases(prefix);
        if (unbounded_grammar_) {
            if (invariant_mode_ && synth_functions_.size() != 1) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unbounded invariant encoding requires one synth-inv");
                return nullptr;
            }
            unbounded_synth_wrappers_.clear();
            if (synth_functions_.size() > 1 || !universal_variables_.empty()) {
                for (std::size_t i = 0; i < synth_functions_.size(); ++i) {
                    unbounded_synth_wrappers_.emplace(
                        synth_functions_[i].name,
                        prefix + "function_" + std::to_string(i));
                }
            }
            for (std::size_t i = 0; i < synth_functions_.size(); ++i) {
                if (!prepareUnboundedAstGrammar(i, prefix, diagnostics)) { return nullptr; }
                SynthFunction& function = synth_functions_[i];
                function.candidates = {unbounded_candidate_};
                function.bindings = {std::vector<S::ChoiceAlternative::Binding>{}};
                function.unbounded_ast = true;
                function.unbounded_prelude = unbounded_prelude_;
                function.unbounded_source_term_placeholder =
                    unbounded_source_term_placeholder_;
                function.unbounded_source_term_symbol = unbounded_source_term_symbol_;
            }
            // Each source definition is fixed across all universal inputs.
            // A helper or grammar leaf may capture globals even for a nullary
            // synth-fun. Wrapper equations enforce that independence; direct
            // substitution of eval(tree, globals) alone would allow f() = x.
            if (synth_functions_.size() == 1 && universal_variables_.empty()) {
                return parseSingleFunction(prefix, diagnostics, report);
            }
        } else if (!enumerateCandidates(prefix, diagnostics)) {
            return nullptr;
        }
        if (!unbounded_grammar_ && synth_functions_.size() == 1
            && !synth_functions_.front().compact_grammar
            && !synth_functions_.front().empty_bounded_grammar) {
            bool captures_universal = false;
            if (!singleFunctionCandidatesCaptureUniversals(
                    synth_functions_.front(), captures_universal, diagnostics)) {
                return nullptr;
            }
            if (!captures_universal) {
                return parseSingleFunction(prefix, diagnostics, report);
            }
        }

        std::ostringstream script;
        script << "(set-logic ALL)\n";

        for (const SynthFunction& function : synth_functions_) {
            if (function.compact_grammar) {
                for (const S::ChoiceAlternative::Binding& binding :
                     function.compact_bindings) {
                    script << "(declare-const " << binding.target_name << ' '
                           << (binding.kind == S::ChoiceAlternative::Binding::Kind::BITVECTOR
                                   ? "(_ BitVec " + std::to_string(binding.bit_width) + ")"
                               : binding.kind == S::ChoiceAlternative::Binding::Kind::BOOLEAN
                                   ? "Bool" : "Int")
                           << ")\n";
                    if (binding.kind == S::ChoiceAlternative::Binding::Kind::INTEGER) {
                        script << "(assert (>= " << binding.target_name << " 0))\n";
                    }
                }
                for (std::size_t i = 0; i < function.grammar_choice.nodes.size(); ++i) {
                    const auto& node = function.grammar_choice.nodes[i];
                    if (node.selector_target.empty()) { continue; }
                    script << "(declare-const " << node.selector_target << " Int)\n"
                           << "(assert (and (<= 0 " << node.selector_target << ") (< "
                           << node.selector_target << ' ' << node.alternatives.size()
                           << ")))\n";
                }
                continue;
            }
            for (const auto& bindings : function.bindings) {
                for (const S::ChoiceAlternative::Binding& binding : bindings) {
                    script << "(declare-const " << binding.target_name << ' '
                           << (binding.kind == S::ChoiceAlternative::Binding::Kind::BITVECTOR
                                   ? "(_ BitVec " + std::to_string(binding.bit_width) + ")"
                                   : "Int")
                           << ")\n";
                }
            }
        }

        std::map<std::string, std::string> wrappers;
        for (std::size_t fi = 0; fi < synth_functions_.size(); ++fi) {
            SynthFunction& function = synth_functions_[fi];
            const std::string wrapper = prefix + "function_" + std::to_string(fi);
            wrappers.emplace(function.name, wrapper);
            std::vector<std::string> domains;
            for (const Typed& parameter : function.parameters) {
                domains.push_back(parameter.sort);
            }
            script << "(declare-fun " << wrapper << " (" << join(domains, " ")
                   << ") " << function.return_sort << ")\n";
            if (function.empty_bounded_grammar) {
                // No program is derivable at this depth. Keep its typed
                // wrapper so all source constraints/helpers are still checked;
                // do not manufacture a candidate or increase the depth.
                script << "(assert false)\n";
                continue;
            }
            std::vector<std::string> selectors;
            if (!function.compact_grammar) {
                for (std::size_t i = 0; i < function.candidates.size(); ++i) {
                    function.selectors.push_back(prefix + "candidate_"
                                                 + std::to_string(fi) + "_"
                                                 + std::to_string(i));
                    script << "(declare-fun " << function.selectors.back() << " () Bool)\n";
                    selectors.push_back("(ite " + function.selectors.back() + " 1 0)");
                    for (const S::ChoiceAlternative::Binding& binding : function.bindings[i]) {
                        if (binding.kind == S::ChoiceAlternative::Binding::Kind::INTEGER) {
                            script << "(assert (>= " << binding.target_name << " 0))\n";
                        }
                    }
                }
            }
            if (!function.compact_grammar) {
                script << "(assert (= "
                       << (selectors.size() == 1 ? selectors.front()
                                                 : "(+ " + join(selectors, " ") + ")")
                       << " 1))\n";
            }
        }
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            if (!definition_dependent_[i]) {
                Sexp renamed = definitions_[i];
                renamed.list[1] = symbolSexp(source_helper_targets_.at(renamed.list[1].atom));
                std::set<std::string> shadowed;
                for (const Typed& parameter : definition_parameters_[i]) {
                    shadowed.insert(parameter.name);
                }
                renamed.list[4] = closeExpression(renameSynthReferences(
                    definitions_[i].list[4], {}, shadowed, source_helper_targets_), shadowed);
                appendClosureParameters(renamed, i);
                script << printSexp(renamed) << '\n';
            }
        }
        std::vector<std::string> wrapper_equations;
        for (std::size_t fi = 0; fi < synth_functions_.size(); ++fi) {
            SynthFunction& function = synth_functions_[fi];
            if (function.empty_bounded_grammar) { continue; }
            const std::string wrapper = wrappers.at(function.name);
            std::set<std::string> parameter_names;
            for (const Typed& parameter : function.parameters) {
                parameter_names.insert(parameter.name);
            }
            std::string body;
            if (function.compact_grammar) {
                // Each grammar production was rewritten before the circuit
                // body was assembled. Reparsing the full nested-let body here
                // would recurse once per grammar depth and duplicate a large
                // generated S-expression tree.
                body = function.compact_smt_body;
            } else {
                std::string rewritten_body;
                if (!renameHelperCalls(function.candidates.back(), source_helper_targets_,
                                       parameter_names, rewritten_body, diagnostics)) {
                    return nullptr;
                }
                body = rewritten_body;
                for (std::size_t i = function.candidates.size() - 1; i-- > 0;) {
                    if (!renameHelperCalls(function.candidates[i], source_helper_targets_,
                                           parameter_names, rewritten_body, diagnostics)) {
                        return nullptr;
                    }
                    body = "(ite " + function.selectors[i] + " "
                         + rewritten_body + " " + body + ")";
                }
            }
            std::vector<std::string> arguments;
            for (const Typed& parameter : function.parameters) {
                arguments.push_back(renderSymbol(parameter.name));
            }
            const std::string call = arguments.empty()
                                         ? wrapper
                                         : "(" + wrapper + " " + join(arguments, " ") + ")";
            std::vector<Typed> closure_binders = function.parameters;
            for (const Typed& global : target_universal_variables_) {
                if (parameter_names.count(global.name) == 0) {
                    closure_binders.push_back(global);
                }
            }
            wrapper_equations.push_back(
                "(assert " + quantify(binder(closure_binders),
                    "(= " + call + " " + body + ")") + ")");
        }
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            if (definition_dependent_[i]) {
                Sexp renamed = definitions_[i];
                std::set<std::string> shadowed;
                for (const Typed& parameter : definition_parameters_[i]) {
                    shadowed.insert(parameter.name);
                }
                renamed.list[4] = closeExpression(renameSynthReferences(
                    definitions_[i].list[4], wrappers, shadowed,
                    source_helper_targets_), shadowed);
                appendClosureParameters(renamed, i);
                renamed.list[1] = symbolSexp(source_helper_targets_.at(renamed.list[1].atom));
                script << printSexp(renamed) << '\n';
            }
        }
        for (const SynthFunction& function : synth_functions_) {
            if (function.unbounded_ast) { script << function.unbounded_prelude; }
        }
        for (const std::string& equation : wrapper_equations) {
            script << equation << '\n';
        }
        const Sexp rewritten_constraints = [&]() {
            Sexp all;
            for (const Sexp& constraint : constraints_) {
                all.list.push_back(closeExpression(renameSynthReferences(
                    constraint, wrappers, {}, source_helper_targets_), {}));
            }
            return all;
        }();
        std::vector<std::string> candidate_constraints;
        for (const Sexp& constraint : rewritten_constraints.list) {
            candidate_constraints.push_back(printSexp(constraint));
        }
        script << "(assert " << quantify(binder(target_universal_variables_),
                                          conjoin(candidate_constraints)) << ")\n";
        script << "(check-sat)\n";

        for (const SynthFunction& function : synth_functions_) {
            if (function.empty_bounded_grammar) {
                Uir::EncodingChoice choice;
                choice.site = function.name;
                choice.unified_op = "syntax-guided-function-synthesis";
                choice.strategy = "empty-bounded-grammar";
                Uir::Fidelity::Bound bound;
                bound.kind = Uir::Fidelity::Bound::GRAMMAR_RESTRICTION;
                bound.value = static_cast<int64_t>(depth_);
                bound.site = function.name;
                choice.fidelity = Uir::Fidelity::underApprox(bound);
                choice.rationale =
                    "the validated grammar has no derivation within grammar_depth="
                    + std::to_string(depth_)
                    + "; an explicit false assertion makes the bounded synthesis "
                      "problem unsatisfiable, so there is no definition witness to project; "
                      "all other grammar productions, helpers and source constraints "
                      "are still checked";
                report.addChoice(std::move(choice));
                continue;
            }
            if (function.compact_grammar) {
                projection_.grammar_choices.push_back(function.grammar_choice);
                for (std::size_t node_index = 0;
                     node_index < function.grammar_choice.nodes.size(); ++node_index) {
                    if (function.grammar_choice.nodes[node_index].selector_target.empty()) {
                        continue;
                    }
                    const std::string selector_source = "grammar-choice["
                        + function.name + "," + std::to_string(node_index) + "]";
                    const std::string& selector_target =
                        function.grammar_choice.nodes[node_index].selector_target;
                    source_signature_.symbols.push_back(
                        {selector_source, S::SymbolKind::CONSTANT, {}, H::Sort::integer()});
                    symbol_map_.push_back({selector_source, selector_target});
                }
                for (std::size_t binding_index = 0;
                     binding_index < function.compact_bindings.size(); ++binding_index) {
                    const auto& binding = function.compact_bindings[binding_index];
                    const std::string constant = "grammar-constant[" + function.name + ","
                                               + std::to_string(binding_index) + "]";
                    source_signature_.symbols.push_back(
                         {constant, S::SymbolKind::CONSTANT, {},
                         binding.kind == S::ChoiceAlternative::Binding::Kind::BITVECTOR
                             ? H::Sort::bitvec(binding.bit_width)
                         : binding.kind == S::ChoiceAlternative::Binding::Kind::BOOLEAN
                             ? H::Sort::boolean() : H::Sort::integer()});
                    symbol_map_.push_back({constant, binding.target_name});
                }
                Uir::EncodingChoice choice;
                choice.site = function.name;
                choice.unified_op = "syntax-guided-function-synthesis";
                choice.strategy = "bounded-grammar-selector-circuit";
                Uir::Fidelity::Bound bound;
                bound.kind = Uir::Fidelity::Bound::GRAMMAR_RESTRICTION;
                bound.value = static_cast<int64_t>(depth_);
                bound.site = function.name;
                choice.fidelity = Uir::Fidelity::underApprox(bound);
                choice.rationale =
                    "integer selectors choose one productive production at each active "
                    "grammar occurrence; the selected derivation is shared across all "
                    "universally quantified inputs and projected as a complete source "
                    "define-fun at grammar_depth=" + std::to_string(depth_)
                    + "; duplicate grammar derivations may decode to the same witness, "
                      "so this encoding makes no derivation-count preservation claim";
                report.addChoice(std::move(choice));
                continue;
            }
            S::ChoiceObservable definition_choice;
            definition_choice.source_name = "definition[" + function.name + "]";
            if (function.unbounded_ast) {
                S::ChoiceAlternative alternative;
                alternative.target_name = function.selectors.front();
                alternative.label = defineFun(function,
                    renderSymbol(function.unbounded_source_term_placeholder));
                S::ChoiceAlternative::Binding witness_binding;
                witness_binding.placeholder = function.unbounded_source_term_placeholder;
                witness_binding.target_name = function.unbounded_direct_constant
                    ? function.witness_value_target : function.witness_text_target;
                witness_binding.kind = S::ChoiceAlternative::Binding::Kind::SMT_TERM;
                if (function.unbounded_direct_constant) {
                    switch (function.return_hir_sort.kind) {
                    case H::SortKind::INT:
                        witness_binding.kind = S::ChoiceAlternative::Binding::Kind::INTEGER;
                        break;
                    case H::SortKind::BOOL:
                        witness_binding.kind = S::ChoiceAlternative::Binding::Kind::BOOLEAN;
                        break;
                    case H::SortKind::BITVEC:
                        witness_binding.kind = S::ChoiceAlternative::Binding::Kind::BITVECTOR;
                        witness_binding.bit_width = function.return_hir_sort.width;
                        break;
                    case H::SortKind::STRING:
                        witness_binding.kind = S::ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE;
                        break;
                    default:
                        diagnostics.error(ErrorCode::E_INTERNAL,
                                          "direct constant grammar has an unsupported result sort");
                        return nullptr;
                    }
                }
                alternative.bindings.push_back(std::move(witness_binding));
                definition_choice.alternatives.push_back(std::move(alternative));
                projection_.choices.push_back(std::move(definition_choice));

                source_signature_.symbols.push_back(
                    {function.unbounded_source_term_symbol, S::SymbolKind::CONSTANT, {},
                     function.unbounded_direct_constant ? function.return_hir_sort
                                                        : H::Sort::string()});
                symbol_map_.push_back({function.unbounded_source_term_symbol,
                    function.unbounded_direct_constant ? function.witness_value_target
                                                       : function.witness_text_target});
                const std::string derivation = "derivation[" + function.name + ",0]";
                source_signature_.symbols.push_back(
                    {derivation, S::SymbolKind::CONSTANT, {}, H::Sort::boolean()});
                symbol_map_.push_back({derivation, function.selectors.front()});

                Uir::EncodingChoice choice;
                choice.site = function.name;
                choice.unified_op = "syntax-guided-function-synthesis";
                choice.strategy = function.unbounded_direct_constant
                    ? "unbounded-grammar-direct-constant"
                    : "unbounded-grammar-adt-recursive-evaluator";
                choice.fidelity = Uir::Fidelity::exact();
                choice.fidelity.count_status = Uir::CountStatus::NO_GUARANTEE;
                choice.rationale =
                    "one inductive AST value ranges over every finite derivation of the "
                    "explicit grammar; all synthesized functions share the same universally "
                    "closed constraints and each AST has its own target-rendered source "
                    "witness. Ambiguous derivations may denote the same function, so "
                    "derivation counts are not preserved";
                if (function.unbounded_direct_constant) {
                    choice.rationale =
                        "one typed target value ranges over the root Constant production "
                        "and is projected as its source literal; all synthesized functions "
                        "share one universally closed specification and retain independent "
                        "definition witnesses";
                }
                if (logic_name_ == "BV" && function.default_grammar_requested) {
                    choice.rationale +=
                        "; omitted grammars use the supported SyGuS-IF B.3 bit-vector "
                        "operator fragment plus listed common extensions, not every term "
                        "allowed by the standard's unrestricted default grammar";
                }
                report.addChoice(std::move(choice));
                continue;
            }
            for (std::size_t i = 0; i < function.candidates.size(); ++i) {
                S::ChoiceAlternative alternative;
                alternative.target_name = function.selectors[i];
                alternative.label = defineFun(function, function.candidates[i]);
                alternative.bindings = function.bindings[i];
                definition_choice.alternatives.push_back(std::move(alternative));
                const std::string derivation = "derivation[" + function.name + ","
                                             + std::to_string(i) + "]";
                source_signature_.symbols.push_back(
                    {derivation, S::SymbolKind::CONSTANT, {}, H::Sort::boolean()});
                symbol_map_.push_back({derivation, function.selectors[i]});
                for (std::size_t j = 0; j < function.bindings[i].size(); ++j) {
                    const auto& binding = function.bindings[i][j];
                    const std::string constant = "constant[" + function.name + ","
                                               + std::to_string(i) + ","
                                               + std::to_string(j) + "]";
                    source_signature_.symbols.push_back(
                        {constant, S::SymbolKind::CONSTANT, {},
                         binding.kind == S::ChoiceAlternative::Binding::Kind::BITVECTOR
                             ? H::Sort::bitvec(binding.bit_width)
                             : H::Sort::integer()});
                    symbol_map_.push_back({constant, binding.target_name});
                }
            }
            projection_.choices.push_back(std::move(definition_choice));

            Uir::EncodingChoice choice;
            choice.site = function.name;
            choice.unified_op = "syntax-guided-function-synthesis";
            choice.strategy = "finite-grammar-depth-enumeration";
            Uir::Fidelity::Bound bound;
            bound.kind = Uir::Fidelity::Bound::GRAMMAR_RESTRICTION;
            bound.value = static_cast<int64_t>(depth_);
            bound.site = function.name;
            choice.fidelity = Uir::Fidelity::underApprox(bound);
            choice.rationale =
                "a shared target model selects one depth-bounded grammar term for each "
                "synthesized function and checks all original constraints jointly";
            if (logic_name_ == "BV" && function.default_grammar_requested) {
                choice.rationale +=
                    "; omitted grammars use the supported SyGuS-IF B.3 bit-vector "
                    "operator fragment plus listed common extensions, not every term "
                    "allowed by the standard's unrestricted default grammar";
            }
            report.addChoice(std::move(choice));
        }

        ParserPtr parser = newParser();
        if (!parser->parseStr(script.str())) {
            diagnostics.error(
                ErrorCode::E_TYPE,
                "the accepted SyGuS grammar/constraints do not form a well-sorted "
                "SMT-LIB formula after grammar elaboration");
            return nullptr;
        }
        auto model = std::make_shared<H::ConstraintModel>();
        Lower::ParserToHir lifter(parser);
        if (!lifter.lift(*model, diagnostics, unbounded_grammar_)) { return nullptr; }
        for (const SynthFunction& function : synth_functions_) {
            if (function.empty_bounded_grammar) {
                target_axioms_.push_back(H::mkBool(false));
                continue;
            }
            if (function.compact_grammar) {
                for (const S::GrammarChoiceNode& node : function.grammar_choice.nodes) {
                    if (node.selector_target.empty()) { continue; }
                    const H::ExprPtr selector = H::mkIdent(
                        node.selector_target, H::Sort::integer());
                    target_axioms_.push_back(H::mkOp(
                        H::Op::LE, {H::mkInt(0), selector}));
                    target_axioms_.push_back(H::mkOp(
                        H::Op::LT, {selector,
                                    H::mkInt(static_cast<int64_t>(node.alternatives.size()))}));
                }
                for (const S::ChoiceAlternative::Binding& binding :
                     function.compact_bindings) {
                    if (binding.kind == S::ChoiceAlternative::Binding::Kind::INTEGER) {
                        target_axioms_.push_back(H::mkOp(
                            H::Op::GE,
                            {H::mkIdent(binding.target_name, H::Sort::integer()),
                             H::mkInt(0)}));
                    }
                }
                continue;
            }
            std::vector<H::ExprPtr> selector_count_exprs;
            for (const std::string& target : function.selectors) {
                selector_count_exprs.push_back(H::mkOp(
                    H::Op::ITE,
                    {H::mkIdent(target, H::Sort::boolean()), H::mkInt(1), H::mkInt(0)}));
            }
            H::ExprPtr selector_count = selector_count_exprs.size() == 1
                                            ? selector_count_exprs.front()
                                            : H::mkOp(H::Op::ADD, std::move(selector_count_exprs));
            target_axioms_.push_back(
                H::mkOp(H::Op::EQ, {selector_count, H::mkInt(1)}));
            for (const auto& bindings : function.bindings) {
                for (const S::ChoiceAlternative::Binding& binding : bindings) {
                    if (binding.kind == S::ChoiceAlternative::Binding::Kind::INTEGER) {
                        target_axioms_.push_back(H::mkOp(
                            H::Op::GE,
                            {H::mkIdent(binding.target_name, H::Sort::integer()), H::mkInt(0)}));
                    }
                }
            }
        }
        return model;
    }

    S::ModelProjection projection() const { return projection_; }
    S::Signature sourceSignature() const { return source_signature_; }
    std::vector<S::SymbolMapping> symbolMap() const { return symbol_map_; }
    std::vector<S::Sentence> targetAxioms() const { return target_axioms_; }

private:
    bool singleFunctionCandidatesCaptureUniversals(
        const SynthFunction& function, bool& captures_universal,
        Uir::Diagnostics& diagnostics) const {
        captures_universal = false;
        std::set<std::string> shadowed;
        for (const Typed& parameter : function.parameters) {
            shadowed.insert(parameter.name);
        }

        for (const std::string& text : function.candidates) {
            std::vector<Sexp> roots;
            std::string error;
            SexpReader reader(text);
            if (!reader.readAll(roots, error) || roots.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "generated SyGuS candidate cannot be reparsed for global-capture analysis");
                return false;
            }

            std::set<std::size_t> direct_globals;
            std::set<std::size_t> dependencies;
            collectClosureReferences(roots.front(), shadowed, direct_globals,
                                     dependencies);
            if (!direct_globals.empty()) {
                captures_universal = true;
                return true;
            }
            for (std::size_t dependency : dependencies) {
                if (dependency < definition_global_indices_.size()
                    && !definition_global_indices_[dependency].empty()) {
                    captures_universal = true;
                    return true;
                }
            }
        }
        return true;
    }

    H::ConstraintModelPtr parseSingleFunction(
        const std::string& prefix, Uir::Diagnostics& diagnostics,
        Uir::TranslationReport& report) {
        const SynthFunction& function = synth_functions_.front();
        const std::vector<std::string>& candidates = function.candidates;
        candidate_bindings_ = function.bindings;

        std::vector<Sexp> candidate_roots(candidates.size());
        for (std::size_t i = 0; i < candidates.size(); ++i) {
            std::vector<Sexp> roots;
            std::string candidate_error;
            SexpReader candidate_reader(candidates[i]);
            if (!candidate_reader.readAll(roots, candidate_error) || roots.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "generated SyGuS candidate cannot be reparsed");
                return nullptr;
            }
            candidate_roots[i] = std::move(roots.front());
            canonicalizeLegacyStringOperators(candidate_roots[i]);
        }
        if (!instantiateHelperDefinitions(prefix, candidate_roots, diagnostics)) {
            return nullptr;
        }
        if (function.unbounded_ast) {
            active_candidate_definition_globals_ =
                &candidate_definition_global_indices_.front();
            if (!prepareUnboundedAstGrammar(0, prefix, diagnostics)) { return nullptr; }
            active_candidate_definition_globals_ = nullptr;
        }

        std::ostringstream script;
        script << "(set-logic ALL)\n";
        for (const auto& bindings : candidate_bindings_) {
            for (const S::ChoiceAlternative::Binding& binding : bindings) {
                script << "(declare-const " << binding.target_name << ' '
                       << (binding.kind == S::ChoiceAlternative::Binding::Kind::BITVECTOR
                               ? "(_ BitVec " + std::to_string(binding.bit_width) + ")"
                               : "Int")
                       << ")\n";
            }
        }
        for (std::size_t i = 0; i < candidates.size(); ++i) {
            candidate_targets_.push_back(prefix + "candidate_" + std::to_string(i));
            script << "(declare-fun " << candidate_targets_.back() << " () Bool)\n";
        }
        std::vector<std::string> selector_count_text;
        for (const std::string& selector : candidate_targets_) {
            selector_count_text.push_back("(ite " + selector + " 1 0)");
        }
        script << "(assert (= "
               << (selector_count_text.size() == 1
                       ? selector_count_text.front()
                       : "(+ " + join(selector_count_text, " ") + ")")
               << " 1))\n";
        for (const auto& bindings : candidate_bindings_) {
            for (const S::ChoiceAlternative::Binding& binding : bindings) {
                if (binding.kind == S::ChoiceAlternative::Binding::Kind::INTEGER) {
                    script << "(assert (>= " << binding.target_name << " 0))\n";
                }
            }
        }
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            if (!definition_dependent_[i]) {
                Sexp definition = definitions_[i];
                definition.list[1] = symbolSexp(source_helper_targets_.at(
                    definition.list[1].atom));
                std::set<std::string> shadowed;
                for (const Typed& parameter : definition_parameters_[i]) {
                    shadowed.insert(parameter.name);
                }
                definition.list[4] = renameSynthReferences(
                    definitions_[i].list[4], {}, shadowed, source_helper_targets_);
                definition.list[4] = closeExpression(definition.list[4], shadowed);
                appendClosureParameters(definition, i);
                script << printSexp(definition) << '\n';
            }
        }
        for (std::size_t candidate = 0;
             candidate < candidate_helper_definitions_.size(); ++candidate) {
            active_candidate_definition_globals_ =
                &candidate_definition_global_indices_[candidate];
            const std::vector<Sexp>& definitions = candidate_helper_definitions_[candidate];
            for (const Sexp& definition : definitions) {
                const auto index = closure_definition_targets_.find(definition.list[1].atom);
                if (index == closure_definition_targets_.end()) {
                    diagnostics.error(ErrorCode::E_INTERNAL,
                                      "generated SyGuS helper has no closure metadata");
                    return nullptr;
                }
                Sexp closed = definition;
                std::set<std::string> shadowed;
                for (const Typed& parameter : definition_parameters_[index->second]) {
                    shadowed.insert(parameter.name);
                }
                closed.list[4] = closeExpression(closed.list[4], shadowed);
                appendClosureParameters(closed, index->second);
                script << printSexp(closed) << '\n';
            }
        }
        if (function.unbounded_ast) { script << unbounded_prelude_; }
        for (std::size_t i = 0; i < candidates.size(); ++i) {
            active_candidate_definition_globals_ =
                &candidate_definition_global_indices_[i];
            bool substitution_ok = true;
            std::vector<std::string> candidate_constraints;
            for (const Sexp& constraint : constraints_) {
                Sexp instantiated = substituteFunction(
                    constraint, candidate_roots[i], substitution_ok,
                    candidate_helper_renames_[i]);
                candidate_constraints.push_back(printSexp(
                    closeExpression(instantiated, {})));
            }
            if (!substitution_ok) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "a constraint applies synth-fun '" + function_name_
                                      + "' at the wrong arity");
                return nullptr;
            }
            script << "(assert (=> " << candidate_targets_[i] << ' '
                   << quantify(binder(target_universal_variables_),
                               conjoin(candidate_constraints))
                   << "))\n";

            S::ChoiceAlternative alternative;
            alternative.target_name = candidate_targets_[i];
            if (function.unbounded_ast && function.unbounded_direct_constant) {
                alternative.label = defineFun(
                    function, renderSymbol(unbounded_source_term_placeholder_));
                S::ChoiceAlternative::Binding binding;
                binding.placeholder = unbounded_source_term_placeholder_;
                binding.target_name = function.witness_value_target;
                switch (function.return_hir_sort.kind) {
                case H::SortKind::INT:
                    binding.kind = S::ChoiceAlternative::Binding::Kind::INTEGER;
                    break;
                case H::SortKind::BOOL:
                    binding.kind = S::ChoiceAlternative::Binding::Kind::BOOLEAN;
                    break;
                case H::SortKind::BITVEC:
                    binding.kind = S::ChoiceAlternative::Binding::Kind::BITVECTOR;
                    binding.bit_width = function.return_hir_sort.width;
                    break;
                case H::SortKind::STRING:
                    binding.kind = S::ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE;
                    break;
                default:
                    diagnostics.error(ErrorCode::E_INTERNAL,
                                      "direct constant grammar has an unsupported result sort");
                    return nullptr;
                }
                alternative.bindings.push_back(std::move(binding));
                source_signature_.symbols.push_back(
                    {unbounded_source_term_symbol_, S::SymbolKind::CONSTANT, {},
                     function.return_hir_sort});
                symbol_map_.push_back(
                    {unbounded_source_term_symbol_, function.witness_value_target});
            } else if (function.unbounded_ast) {
                alternative.label = defineFun(
                    function, renderSymbol(unbounded_source_term_placeholder_));
                S::ChoiceAlternative::Binding binding;
                binding.placeholder = unbounded_source_term_placeholder_;
                binding.target_name = function.witness_text_target;
                binding.kind = S::ChoiceAlternative::Binding::Kind::SMT_TERM;
                alternative.bindings.push_back(std::move(binding));
                source_signature_.symbols.push_back(
                    {unbounded_source_term_symbol_, S::SymbolKind::CONSTANT, {},
                     H::Sort::string()});
                symbol_map_.push_back(
                    {unbounded_source_term_symbol_, function.witness_text_target});
            } else {
                alternative.label = defineFun(candidates[i]);
                alternative.bindings = candidate_bindings_[i];
            }
            definition_choice_.alternatives.push_back(std::move(alternative));
            const std::string derivation =
                "derivation[" + function_name_ + "," + std::to_string(i) + "]";
            source_signature_.symbols.push_back(
                {derivation, S::SymbolKind::CONSTANT, {}, H::Sort::boolean()});
            symbol_map_.push_back({derivation, candidate_targets_[i]});
            for (std::size_t j = 0; j < candidate_bindings_[i].size(); ++j) {
                const S::ChoiceAlternative::Binding& binding = candidate_bindings_[i][j];
                const std::string constant = "constant[" + function_name_ + ","
                                           + std::to_string(i) + ","
                                           + std::to_string(j) + "]";
                source_signature_.symbols.push_back(
                    {constant, S::SymbolKind::CONSTANT, {},
                     binding.kind == S::ChoiceAlternative::Binding::Kind::SMT_TERM
                         ? H::Sort::string()
                     : binding.kind == S::ChoiceAlternative::Binding::Kind::BITVECTOR
                         ? H::Sort::bitvec(binding.bit_width)
                         : H::Sort::integer()});
                symbol_map_.push_back({constant, binding.target_name});
            }
        }
        active_candidate_definition_globals_ = nullptr;
        script << "(check-sat)\n";

        ParserPtr parser = newParser();
        if (!parser->parseStr(script.str())) {
            diagnostics.error(
                ErrorCode::E_TYPE,
                "the accepted SyGuS grammar/constraints do not form a well-sorted "
                "SMT-LIB formula after finite elaboration");
            return nullptr;
        }
        auto model = std::make_shared<H::ConstraintModel>();
        Lower::ParserToHir lifter(parser);
        if (!lifter.lift(*model, diagnostics, unbounded_grammar_)) { return nullptr; }
        std::vector<H::ExprPtr> selector_count_exprs;
        for (const std::string& target : candidate_targets_) {
            selector_count_exprs.push_back(H::mkOp(
                H::Op::ITE,
                {H::mkIdent(target, H::Sort::boolean()), H::mkInt(1), H::mkInt(0)}));
        }
        H::ExprPtr selector_count = selector_count_exprs.size() == 1
                                        ? selector_count_exprs.front()
                                        : H::mkOp(H::Op::ADD, std::move(selector_count_exprs));
        target_axioms_.push_back(
            H::mkOp(H::Op::EQ, {selector_count, H::mkInt(1)}));
        for (const auto& bindings : candidate_bindings_) {
            for (const S::ChoiceAlternative::Binding& binding : bindings) {
                if (binding.kind == S::ChoiceAlternative::Binding::Kind::INTEGER) {
                    target_axioms_.push_back(H::mkOp(
                        H::Op::GE,
                        {H::mkIdent(binding.target_name, H::Sort::integer()), H::mkInt(0)}));
                }
            }
        }
        definition_choice_.source_name = "definition[" + function_name_ + "]";
        projection_.choices.push_back(definition_choice_);

        Uir::EncodingChoice choice;
        choice.site = function_name_;
        choice.unified_op = "syntax-guided-function-synthesis";
        if (function.unbounded_ast && function.unbounded_direct_constant) {
            choice.strategy = "unbounded-grammar-direct-constant";
            choice.fidelity = Uir::Fidelity::exact();
            choice.fidelity.count_status = Uir::CountStatus::NO_GUARANTEE;
            choice.rationale =
                "the sole root production (Constant Sort) denotes every value of "
                "the result sort, so one typed target value is exactly equivalent "
                "and serves directly as the source literal witness";
        } else if (function.unbounded_ast) {
            choice.strategy = "unbounded-grammar-adt-recursive-evaluator";
            choice.fidelity = Uir::Fidelity::exact();
            choice.fidelity.count_status = Uir::CountStatus::NO_GUARANTEE;
            choice.rationale =
                "one inductive AST value ranges over every finite derivation of the "
                "explicit grammar; structurally recursive evaluators interpret the "
                "selected tree, and a target renderer projects an exact source "
                "define-fun witness. Ambiguous derivations can denote the same "
                "function, so derivation counts are not preserved";
        } else {
            choice.strategy = "finite-grammar-depth-enumeration";
            Uir::Fidelity::Bound bound;
            bound.kind = Uir::Fidelity::Bound::GRAMMAR_RESTRICTION;
            bound.value = static_cast<int64_t>(depth_);
            bound.site = function_name_;
            choice.fidelity = Uir::Fidelity::underApprox(bound);
            choice.rationale =
                "one candidate selector entails the original specification under its "
                "universal closure; SAT returns a grammar-derived define-fun, while "
                "UNSAT excludes only candidates within grammar_depth="
                + std::to_string(depth_);
        }
        if (logic_name_ == "BV" && function.default_grammar_requested) {
            choice.rationale +=
                "; omitted grammars use the supported SyGuS-IF B.3 bit-vector "
                "operator fragment plus listed common extensions, not every term "
                "allowed by the standard's unrestricted default grammar";
        }
        report.addChoice(std::move(choice));
        return model;
    }

    bool sort(const Sexp& expression, std::string& text, H::Sort& hir,
              Uir::Diagnostics& diagnostics) const {
        if (expression.isAtom() && expression.atom == "Int") {
            text = "Int";
            hir = H::Sort::integer();
            return true;
        }
        if (expression.isAtom() && expression.atom == "Bool") {
            text = "Bool";
            hir = H::Sort::boolean();
            return true;
        }
        if (expression.isAtom() && expression.atom == "String") {
            text = "String";
            hir = H::Sort::string();
            return true;
        }
        const bool indexed_bv = !expression.isAtom() && expression.list.size() == 3
            && expression.list[0].isAtom() && expression.list[0].atom == "_"
            && expression.list[1].isAtom() && expression.list[1].atom == "BitVec"
            && expression.list[2].isAtom();
        const bool legacy_bv = !expression.isAtom() && expression.list.size() == 2
            && expression.list[0].isAtom() && expression.list[0].atom == "BitVec"
            && expression.list[1].isAtom();
        if (indexed_bv || legacy_bv) {
            const std::string& width_text = expression.list.back().atom;
            unsigned long width = 0;
            try {
                if (!unsignedDecimal(width_text)) {
                    throw std::invalid_argument("non-decimal BitVec width");
                }
                std::size_t consumed = 0;
                width = std::stoul(width_text, &consumed);
                if (consumed != width_text.size() || width == 0
                    || width > std::numeric_limits<unsigned>::max()) {
                    throw std::out_of_range("BitVec width");
                }
            } catch (const std::exception&) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "SyGuS BitVec sort requires a positive unsigned width");
                return false;
            }
            text = "(_ BitVec " + std::to_string(width) + ")";
            hir = H::Sort::bitvec(static_cast<unsigned>(width));
            return true;
        }
        diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                          "SyGuS sort '" + printSexp(expression)
                              + "' needs a grammar enumerator for its theory");
        return false;
    }

    static Sexp canonicalSort(const H::Sort& hir) {
        if (hir.kind == H::SortKind::BITVEC) {
            return form({atom("_"), atom("BitVec"), atom(std::to_string(hir.width))});
        }
        if (hir.kind == H::SortKind::STRING) { return atom("String"); }
        return atom(hir.kind == H::SortKind::BOOL ? "Bool" : "Int");
    }

    static Sexp indexedSort(unsigned width) {
        return form({atom("_"), atom("BitVec"), atom(std::to_string(width))});
    }

    static bool bitVectorWidth(const std::string& text, unsigned& width) {
        constexpr char prefix[] = "(_ BitVec ";
        if (text.compare(0, sizeof(prefix) - 1, prefix) != 0
            || text.size() <= sizeof(prefix) || text.back() != ')') {
            return false;
        }
        const std::string digits = text.substr(
            sizeof(prefix) - 1, text.size() - sizeof(prefix));
        try {
            if (!unsignedDecimal(digits)) { return false; }
            std::size_t consumed = 0;
            const unsigned long value = std::stoul(digits, &consumed);
            if (consumed != digits.size() || value == 0
                || value > std::numeric_limits<unsigned>::max()) {
                return false;
            }
            width = static_cast<unsigned>(value);
            return true;
        } catch (const std::exception&) {
            return false;
        }
    }

    bool typedBinder(const Sexp& expression, const std::string& context,
                     std::vector<Typed>& result,
                     Uir::Diagnostics& diagnostics) const {
        if (expression.isAtom()) {
            diagnostics.error(ErrorCode::E_PARSE, context + " must be a binder list");
            return false;
        }
        std::set<std::string> names;
        for (const Sexp& binder_entry : expression.list) {
            if (binder_entry.list.size() != 2 || !binder_entry.list[0].isAtom()
                || !simpleSymbol(binder_entry.list[0])) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed binder in " + context);
                return false;
            }
            Typed typed;
            typed.name = binder_entry.list[0].atom;
            if (!names.insert(typed.name).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate binder '" + typed.name + "' in " + context);
                return false;
            }
            if (!sort(binder_entry.list[1], typed.sort, typed.hir_sort, diagnostics)) {
                return false;
            }
            result.push_back(std::move(typed));
        }
        return true;
    }

    bool containsFreeSymbol(const Sexp& expression, const std::string& symbol,
                            const std::set<std::string>& bound) const {
        if (expression.isStringLiteral()) { return false; }
        if (expression.isAtom()) {
            return expression.atom == symbol && bound.count(symbol) == 0;
        }
        if (expression.list.empty()) { return false; }
        if (!expression.list.front().isStringLiteral()
            && expression.head() == symbol && bound.count(symbol) == 0) { return true; }

        if ((expression.head() == "forall" || expression.head() == "exists"
             || expression.head() == "lambda")
            && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            std::set<std::string> nested = bound;
            for (const Sexp& binder_entry : expression.list[1].list) {
                if (binder_entry.list.size() == 2 && binder_entry.list[0].isAtom()) {
                    nested.insert(binder_entry.list[0].atom);
                }
            }
            return containsFreeSymbol(expression.list[2], symbol, nested);
        }
        if (expression.head() == "let" && expression.list.size() == 3
            && !expression.list[1].isAtom()) {
            std::set<std::string> nested = bound;
            for (const Sexp& binding : expression.list[1].list) {
                if (binding.list.size() == 2 && binding.list[0].isAtom()) {
                    if (containsFreeSymbol(binding.list[1], symbol, bound)) { return true; }
                    nested.insert(binding.list[0].atom);
                }
            }
            return containsFreeSymbol(expression.list[2], symbol, nested);
        }
        for (const Sexp& child : expression.list) {
            if (containsFreeSymbol(child, symbol, bound)) { return true; }
        }
        return false;
    }

    struct SourceFunctionSignature {
        std::vector<std::string> arguments;
        std::string result;
    };

    bool normalizeTypedLetExpression(
        const Sexp& expression, const std::map<std::string, std::string>& variables,
        const std::map<std::string, SourceFunctionSignature>& functions,
        Sexp& normalized, std::optional<std::string>& inferred,
        Uir::Diagnostics& diagnostics) const {
        if (expression.isAtom()) {
            normalized = expression;
            if (expression.isStringLiteral()) {
                inferred = "String";
                return true;
            }
            const auto variable = variables.find(expression.atom);
            if (variable != variables.end()) { inferred = variable->second; }
            else if (!expression.quoted_symbol
                     && (expression.atom == "true" || expression.atom == "false")) {
                inferred = "Bool";
            } else if (!expression.quoted_symbol && !expression.atom.empty()
                       && std::all_of(expression.atom.begin(), expression.atom.end(),
                                      [](unsigned char c) { return std::isdigit(c) != 0; })) {
                inferred = "Int";
            } else if (!expression.quoted_symbol && expression.atom.size() > 2
                       && (expression.atom.compare(0, 2, "#b") == 0
                           || expression.atom.compare(0, 2, "#x") == 0)) {
                const bool binary = expression.atom[1] == 'b';
                const std::size_t width = (expression.atom.size() - 2)
                                          * (binary ? 1U : 4U);
                const bool digits_valid = std::all_of(
                    expression.atom.begin() + 2, expression.atom.end(),
                    [binary](unsigned char c) {
                        return binary ? (c == '0' || c == '1') : std::isxdigit(c) != 0;
                    });
                if (digits_valid && width > 0
                    && width <= std::numeric_limits<unsigned>::max()) {
                    inferred = "(_ BitVec " + std::to_string(width) + ")";
                }
            } else {
                const auto function = functions.find(expression.atom);
                if (function != functions.end() && function->second.arguments.empty()) {
                    inferred = function->second.result;
                } else if (function == functions.end() && !expression.quoted_symbol
                           && legacyNegativeInteger(expression.atom)) {
                    normalized = application("-", {atom(expression.atom.substr(1))});
                    inferred = "Int";
                }
            }
            return true;
        }
        if (expression.list.size() == 3 && expression.list[0].isAtom()
            && expression.list[0].atom == "_" && expression.list[1].isAtom()
            && expression.list[1].atom.compare(0, 2, "bv") == 0
            && expression.list[2].isAtom()) {
            const std::string width_text = expression.list[2].atom;
            try {
                if (!unsignedDecimal(width_text)) {
                    throw std::invalid_argument("non-decimal BitVec width");
                }
                std::size_t consumed = 0;
                const unsigned long width = std::stoul(width_text, &consumed);
                if (consumed == width_text.size() && width > 0
                    && width <= std::numeric_limits<unsigned>::max()) {
                    normalized = expression;
                    inferred = "(_ BitVec " + std::to_string(width) + ")";
                    return true;
                }
            } catch (const std::exception&) {
                // Leave malformed terms for the native parser's precise error.
            }
        }
        if (expression.list.size() == 2 && !expression.list[0].isAtom()
            && expression.list[0].list.size() >= 2
            && expression.list[0].list[0].isAtom()
            && expression.list[0].list[0].atom == "_"
            && expression.list[0].list[1].isAtom()) {
            const Sexp& indexed = expression.list[0];
            const std::string& indexed_op = indexed.list[1].atom;
            std::vector<unsigned> indices;
            bool valid_indices = true;
            for (std::size_t i = 2; i < indexed.list.size(); ++i) {
                if (!indexed.list[i].isAtom()) { valid_indices = false; break; }
                try {
                    if (!unsignedDecimal(indexed.list[i].atom)) {
                        valid_indices = false;
                        break;
                    }
                    std::size_t consumed = 0;
                    const unsigned long value = std::stoul(indexed.list[i].atom, &consumed);
                    if (consumed != indexed.list[i].atom.size()
                        || value > std::numeric_limits<unsigned>::max()) {
                        valid_indices = false;
                        break;
                    }
                    indices.push_back(static_cast<unsigned>(value));
                } catch (const std::exception&) {
                    valid_indices = false;
                    break;
                }
            }
            Sexp normalized_argument;
            std::optional<std::string> argument_sort;
            if (!normalizeTypedLetExpression(expression.list[1], variables, functions,
                                             normalized_argument, argument_sort,
                                             diagnostics)) {
                return false;
            }
            normalized.list = {expression.list[0], normalized_argument};
            const auto bit_width = [](const std::optional<std::string>& sort_text)
                -> std::optional<unsigned> {
                constexpr const char prefix[] = "(_ BitVec ";
                if (!sort_text || sort_text->compare(0, sizeof(prefix) - 1, prefix) != 0
                    || sort_text->back() != ')') {
                    return std::nullopt;
                }
                const std::string digits = sort_text->substr(
                    sizeof(prefix) - 1, sort_text->size() - sizeof(prefix));
                try {
                    if (!unsignedDecimal(digits)) { return std::nullopt; }
                    std::size_t consumed = 0;
                    const unsigned long width = std::stoul(digits, &consumed);
                    if (consumed != digits.size() || width == 0
                        || width > std::numeric_limits<unsigned>::max()) {
                        return std::nullopt;
                    }
                    return static_cast<unsigned>(width);
                } catch (const std::exception&) {
                    return std::nullopt;
                }
            };
            if (valid_indices && indexed_op == "extract" && indices.size() == 2) {
                const auto source_width = bit_width(argument_sort);
                if (source_width && indices[0] >= indices[1]
                    && indices[0] < *source_width) {
                    inferred = "(_ BitVec "
                             + std::to_string(indices[0] - indices[1] + 1) + ")";
                }
            } else if (valid_indices && indices.size() == 1
                       && (indexed_op == "zero_extend" || indexed_op == "sign_extend"
                           || indexed_op == "repeat" || indexed_op == "rotate_left"
                           || indexed_op == "rotate_right")) {
                const auto source_width = bit_width(argument_sort);
                if (source_width) {
                    unsigned width = *source_width;
                    if (indexed_op == "zero_extend" || indexed_op == "sign_extend") {
                        if (indices[0] <= std::numeric_limits<unsigned>::max() - width) {
                            width += indices[0];
                            inferred = "(_ BitVec " + std::to_string(width) + ")";
                        }
                    } else if (indexed_op == "repeat") {
                        if (indices[0] > 0
                            && indices[0] <= std::numeric_limits<unsigned>::max() / width) {
                            width *= indices[0];
                            inferred = "(_ BitVec " + std::to_string(width) + ")";
                        }
                    } else {
                        inferred = argument_sort;
                    }
                }
            } else if (valid_indices && indices.size() == 1
                       && (indexed_op == "int2bv" || indexed_op == "int_to_bv")
                       && argument_sort == std::optional<std::string>("Int")
                       && indices[0] > 0) {
                inferred = "(_ BitVec " + std::to_string(indices[0]) + ")";
            }
            return true;
        }
        if (expression.head() == "let" && expression.list.size() == 3
            && !expression.list[1].isAtom()) {
            std::map<std::string, std::string> nested = variables;
            Sexp bindings;
            for (const Sexp& binding : expression.list[1].list) {
                if ((binding.list.size() != 2 && binding.list.size() != 3)
                    || !binding.list[0].isAtom()) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed SyGuS let binding");
                    return false;
                }
                const bool typed = binding.list.size() == 3;
                std::string declared_sort;
                H::Sort declared_hir;
                if (typed && !sort(binding.list[1], declared_sort, declared_hir, diagnostics)) {
                    return false;
                }
                const Sexp& rhs = binding.list[typed ? 2 : 1];
                Sexp normalized_rhs;
                std::optional<std::string> rhs_sort;
                if (!normalizeTypedLetExpression(rhs, variables, functions,
                                                 normalized_rhs, rhs_sort, diagnostics)) {
                    return false;
                }
                if (typed && (!rhs_sort || *rhs_sort != declared_sort)) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "typed let binding '" + binding.list[0].atom
                                          + "' declares " + declared_sort
                                          + " but its value is not of that sort");
                    return false;
                }
                bindings.list.push_back(form({binding.list[0], normalized_rhs}));
                nested.erase(binding.list[0].atom);
                if (typed) { nested[binding.list[0].atom] = declared_sort; }
                else if (rhs_sort) { nested[binding.list[0].atom] = *rhs_sort; }
            }
            Sexp body;
            if (!normalizeTypedLetExpression(expression.list[2], nested, functions,
                                             body, inferred, diagnostics)) {
                return false;
            }
            normalized = form({expression.list[0], bindings, body});
            return true;
        }
        if ((expression.head() == "forall" || expression.head() == "exists")
            && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            std::map<std::string, std::string> nested = variables;
            Sexp binders;
            for (const Sexp& binding : expression.list[1].list) {
                if (binding.list.size() != 2 || !binding.list[0].isAtom()) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed quantified binder in typed let scope");
                    return false;
                }
                std::string binder_sort;
                H::Sort ignored;
                if (!sort(binding.list[1], binder_sort, ignored, diagnostics)) { return false; }
                binders.list.push_back(form({binding.list[0], canonicalSort(ignored)}));
                nested[binding.list[0].atom] = binder_sort;
            }
            Sexp body;
            std::optional<std::string> body_sort;
            if (!normalizeTypedLetExpression(expression.list[2], nested, functions,
                                             body, body_sort, diagnostics)) {
                return false;
            }
            normalized = form({expression.list[0], binders, body});
            if (body_sort == std::optional<std::string>("Bool")) { inferred = "Bool"; }
            return true;
        }

        normalized.list.reserve(expression.list.size());
        std::vector<std::optional<std::string>> argument_sorts;
        for (std::size_t i = 0; i < expression.list.size(); ++i) {
            Sexp child;
            std::optional<std::string> child_sort;
            if (!normalizeTypedLetExpression(expression.list[i], variables, functions,
                                             child, child_sort, diagnostics)) {
                return false;
            }
            normalized.list.push_back(std::move(child));
            if (i != 0) { argument_sorts.push_back(std::move(child_sort)); }
        }
        std::string op = expression.head();
        if (op == "int.to.str" && isBuiltinInSourceLogic(op)) {
            op = "str.from_int";
            normalized.list.front() = atom(op);
        } else if (op == "str.to.int" && isBuiltinInSourceLogic(op)) {
            op = "str.to_int";
            normalized.list.front() = atom(op);
        }
        const auto arity = [&](std::size_t minimum, std::size_t maximum) {
            return argument_sorts.size() >= minimum && argument_sorts.size() <= maximum;
        };
        const auto all = [&](const std::string& expected) {
            return std::all_of(argument_sorts.begin(), argument_sorts.end(),
                               [&](const std::optional<std::string>& value) {
                                   return value && *value == expected;
                               });
        };
        const auto knownSame = [&]() -> std::optional<std::string> {
            std::optional<std::string> first;
            for (const auto& value : argument_sorts) {
                if (!value) { return std::nullopt; }
                if (first && *first != *value) { return std::nullopt; }
                first = value;
            }
            return first;
        };
        const auto bitVectorWidth = [](const std::optional<std::string>& sort_text)
            -> std::optional<unsigned> {
            constexpr char prefix[] = "(_ BitVec ";
            if (!sort_text || sort_text->compare(0, sizeof(prefix) - 1, prefix) != 0
                || sort_text->size() <= sizeof(prefix)
                || sort_text->back() != ')') {
                return std::nullopt;
            }
            const std::string digits = sort_text->substr(
                sizeof(prefix) - 1, sort_text->size() - sizeof(prefix));
            try {
                if (!unsignedDecimal(digits)) { return std::nullopt; }
                std::size_t consumed = 0;
                const unsigned long width = std::stoul(digits, &consumed);
                if (consumed != digits.size() || width == 0
                    || width > std::numeric_limits<unsigned>::max()) {
                    return std::nullopt;
                }
                return static_cast<unsigned>(width);
            } catch (const std::exception&) {
                return std::nullopt;
            }
        };
        if (op == "str.++") {
            if (arity(2, SIZE_MAX) && all("String")) { inferred = "String"; }
        } else if (op == "str.replace") {
            if (arity(3, 3) && all("String")) { inferred = "String"; }
        } else if (op == "str.at") {
            if (arity(2, 2) && argument_sorts[0] == std::optional<std::string>("String")
                && argument_sorts[1] == std::optional<std::string>("Int")) {
                inferred = "String";
            }
        } else if (op == "str.substr") {
            if (arity(3, 3) && argument_sorts[0] == std::optional<std::string>("String")
                && argument_sorts[1] == std::optional<std::string>("Int")
                && argument_sorts[2] == std::optional<std::string>("Int")) {
                inferred = "String";
            }
        } else if (op == "str.len") {
            if (arity(1, 1) && all("String")) { inferred = "Int"; }
        } else if (op == "str.to_int") {
            if (arity(1, 1) && all("String")) { inferred = "Int"; }
        } else if (op == "str.from_int") {
            if (arity(1, 1) && all("Int")) { inferred = "String"; }
        } else if (op == "str.indexof") {
            if (arity(3, 3) && argument_sorts[0] == std::optional<std::string>("String")
                && argument_sorts[1] == std::optional<std::string>("String")
                && argument_sorts[2] == std::optional<std::string>("Int")) {
                inferred = "Int";
            }
        } else if (op == "str.contains" || op == "str.prefixof"
                   || op == "str.suffixof") {
            if (arity(2, 2) && all("String")) { inferred = "Bool"; }
        } else if (op == "and" || op == "or" || op == "xor" || op == "=>") {
            if (arity(2, SIZE_MAX) && all("Bool")) { inferred = "Bool"; }
        } else if (op == "not") {
            if (arity(1, 1) && all("Bool")) { inferred = "Bool"; }
        } else if (op == "=" || op == "distinct") {
            if (arity(2, SIZE_MAX) && knownSame()) { inferred = "Bool"; }
        } else if (op == "<" || op == "<=" || op == ">" || op == ">=") {
            if (arity(2, SIZE_MAX) && all("Int")) { inferred = "Bool"; }
        } else if (op == "+" || op == "*") {
            if (arity(2, SIZE_MAX) && all("Int")) { inferred = "Int"; }
        } else if (op == "-") {
            if (arity(1, SIZE_MAX) && all("Int")) { inferred = "Int"; }
        } else if (op == "div" || op == "mod") {
            if (arity(2, 2) && all("Int")) { inferred = "Int"; }
        } else if (op == "abs") {
            if (arity(1, 1) && all("Int")) { inferred = "Int"; }
        } else if (op == "bvnot" || op == "bvneg") {
            if (arity(1, 1) && argument_sorts[0]
                && argument_sorts[0]->rfind("(_ BitVec ", 0) == 0) {
                inferred = argument_sorts[0];
            }
        } else if (op == "bvand" || op == "bvor" || op == "bvxor"
                   || op == "bvnand" || op == "bvnor" || op == "bvxnor"
                   || op == "bvadd" || op == "bvsub" || op == "bvmul"
                   || op == "bvudiv" || op == "bvurem" || op == "bvsdiv"
                   || op == "bvsrem" || op == "bvsmod" || op == "bvshl"
                   || op == "bvlshr" || op == "bvashr") {
            const bool left_associative = op == "bvand" || op == "bvor"
                                          || op == "bvadd" || op == "bvmul";
            const bool matching_bitvectors = !argument_sorts.empty()
                && argument_sorts[0]
                && argument_sorts[0]->rfind("(_ BitVec ", 0) == 0
                && std::all_of(argument_sorts.begin() + 1, argument_sorts.end(),
                               [&](const std::optional<std::string>& argument) {
                                   return argument && argument == argument_sorts[0];
                               });
            if (arity(2, left_associative ? SIZE_MAX : 2)
                && matching_bitvectors) {
                inferred = argument_sorts[0];
            }
        } else if (op == "bvult" || op == "bvule" || op == "bvugt"
                   || op == "bvuge" || op == "bvslt" || op == "bvsle"
                   || op == "bvsgt" || op == "bvsge") {
            if (arity(2, 2) && argument_sorts[0]
                && argument_sorts[0]->rfind("(_ BitVec ", 0) == 0
                && argument_sorts[0] == argument_sorts[1]) {
                inferred = "Bool";
            }
        } else if (op == "concat") {
            if (arity(2, 2)) {
                const auto left_width = bitVectorWidth(argument_sorts[0]);
                const auto right_width = bitVectorWidth(argument_sorts[1]);
                if (left_width && right_width) {
                    if (*right_width > std::numeric_limits<unsigned>::max() - *left_width) {
                        diagnostics.error(ErrorCode::E_RESOURCE,
                                          "SyGuS concat result width overflows unsigned range");
                        return false;
                    }
                    inferred = "(_ BitVec "
                             + std::to_string(*left_width + *right_width) + ")";
                }
            }
        } else if (op == "bvcomp") {
            if (arity(2, 2) && bitVectorWidth(argument_sorts[0])
                && argument_sorts[0] == argument_sorts[1]) {
                inferred = "(_ BitVec 1)";
            }
        } else if (op == "bv2int" || op == "bv2nat"
                   || op == "ubv_to_int" || op == "sbv_to_int") {
            if (arity(1, 1) && bitVectorWidth(argument_sorts[0])) {
                inferred = "Int";
            }
        } else if (op == "ite" && argument_sorts.size() == 3) {
            if (argument_sorts[0] == std::optional<std::string>("Bool")
                && argument_sorts[1] && argument_sorts[2]
                && argument_sorts[1] == argument_sorts[2]) {
                inferred = argument_sorts[1];
            }
        } else if ((op == "forall" || op == "exists")
                   && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            inferred = "Bool";
        } else {
            const auto function = functions.find(op);
            if (function != functions.end()) {
                bool arguments_known =
                    function->second.arguments.size() == argument_sorts.size();
                for (std::size_t i = 0; i < argument_sorts.size(); ++i) {
                    arguments_known = arguments_known && argument_sorts[i]
                        && *argument_sorts[i] == function->second.arguments[i];
                }
                if (arguments_known) {
                    inferred = function->second.result;
                }
            }
        }
        return true;
    }

    bool normalizeTypedLetSources(Uir::Diagnostics& diagnostics) {
        std::map<std::string, SourceFunctionSignature> functions;
        for (const SynthFunction& synth : synth_functions_) {
            SourceFunctionSignature signature;
            for (const Typed& parameter : synth.parameters) {
                signature.arguments.push_back(parameter.sort);
            }
            signature.result = synth.return_sort;
            functions[synth.name] = std::move(signature);
        }
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            const Sexp& definition = definitions_[i];
            SourceFunctionSignature signature;
            for (const Typed& parameter : definition_parameters_[i]) {
                signature.arguments.push_back(parameter.sort);
            }
            H::Sort ignored;
            if (!sort(definition.list[3], signature.result, ignored, diagnostics)) { return false; }
            // Register the current symbol so recursive references receive an
            // accurate RHS type; validateDefinitions later rejects recursion.
            functions[definition.list[1].atom] = signature;
            std::map<std::string, std::string> variables;
            for (const Typed& global : universal_variables_) {
                if (definition_visible_universals_[i].count(global.name) != 0) {
                    variables[global.name] = global.sort;
                }
            }
            for (const Typed& parameter : definition_parameters_[i]) {
                // Function parameters are lexically inside the global
                // signature and may shadow a declare-var of the same name.
                variables[parameter.name] = parameter.sort;
            }
            Sexp body;
            std::optional<std::string> body_sort;
            if (!normalizeTypedLetExpression(definition.list[4], variables, functions,
                                             body, body_sort, diagnostics)) {
                return false;
            }
            definitions_[i].list[4] = std::move(body);
        }
        std::map<std::string, std::string> globals;
        for (const Typed& variable : universal_variables_) {
            globals[variable.name] = variable.sort;
        }
        for (Sexp& constraint : constraints_) {
            Sexp normalized;
            std::optional<std::string> ignored_sort;
            if (!normalizeTypedLetExpression(constraint, globals, functions,
                                             normalized, ignored_sort, diagnostics)) {
                return false;
            }
            constraint = std::move(normalized);
        }
        return true;
    }

    bool validateDefinitions(Uir::Diagnostics& diagnostics) {
        definition_dependent_.assign(definitions_.size(), false);
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            const Sexp& command = definitions_[i];
            const std::string& name = command.list[1].atom;
            std::set<std::string> bound;
            for (const Typed& parameter : definition_parameters_[i]) {
                bound.insert(parameter.name);
            }
            const Sexp& body = command.list[4];
            if (containsFreeSymbol(body, name, bound)) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "recursive SyGuS define-fun '" + name
                                      + "' is not permitted");
                return false;
            }
            for (const Typed& global : universal_variables_) {
                if (definition_visible_universals_[i].count(global.name) == 0
                    && containsFreeSymbol(body, global.name, bound)) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "define-fun '" + name
                                          + "' refers to undeclared universal '"
                                          + global.name + "'");
                    return false;
                }
            }
            for (const SynthFunction& synth : synth_functions_) {
                if (!containsFreeSymbol(body, synth.name, bound)) { continue; }
                if (definition_visible_synths_[i].count(synth.name) == 0) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "define-fun '" + name
                                          + "' refers to synth-fun '" + synth.name
                                          + "' before its declaration");
                    return false;
                }
                definition_dependent_[i] = true;
            }
            for (std::size_t j = 0; j < definitions_.size(); ++j) {
                const std::string& dependency = definitions_[j].list[1].atom;
                if (dependency == name || !containsFreeSymbol(body, dependency, bound)) {
                    continue;
                }
                if (j >= i) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "define-fun '" + name
                                          + "' has a recursive or forward reference to '"
                                          + dependency + "'");
                    return false;
                }
                if (definition_dependent_[j]) { definition_dependent_[i] = true; }
            }
        }
        return true;
    }

    bool elaborateInvariantConstraints(Uir::Diagnostics& diagnostics) {
        if (!invariant_mode_ && invariant_constraints_.empty()) { return true; }
        if (!invariant_mode_ || invariant_constraints_.empty()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "synth-inv requires at least one inv-constraint");
            return false;
        }
        const auto findDefinition = [&](const std::string& name) -> std::size_t {
            for (std::size_t i = 0; i < definitions_.size(); ++i) {
                if (definitions_[i].list[1].atom == name) { return i; }
            }
            return definitions_.size();
        };
        const auto call = [&](const std::string& name,
                              const std::vector<std::string>& arguments) {
            if (arguments.empty()) { return symbolSexp(name); }
            Sexp result;
            result.list.push_back(symbolSexp(name));
            for (const std::string& argument : arguments) {
                result.list.push_back(symbolSexp(argument));
            }
            return result;
        };
        std::vector<std::string> current;
        std::vector<std::string> next;
        for (const Typed& parameter : parameters_) {
            current.push_back(parameter.name);
            next.push_back(parameter.name + "!");
            for (const std::string& name : {parameter.name, parameter.name + "!"}) {
                const auto declared = std::find_if(
                    universal_variables_.begin(), universal_variables_.end(),
                    [&](const Typed& variable) { return variable.name == name; });
                if (declared == universal_variables_.end()
                    || !H::sameSort(declared->hir_sort, parameter.hir_sort)) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "invariant state variable '" + parameter.name
                                          + "' and its primed version must be declared with matching sorts");
                    return false;
                }
            }
        }
        for (const Sexp& command : invariant_constraints_) {
            const std::string& inv_name = command.list[1].atom;
            const std::size_t pre = findDefinition(command.list[2].atom);
            const std::size_t trans = findDefinition(command.list[3].atom);
            const std::size_t post = findDefinition(command.list[4].atom);
            if (inv_name != function_name_ || pre == definitions_.size()
                || trans == definitions_.size() || post == definitions_.size()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "inv-constraint must name the synthesized invariant and three define-fun functions");
                return false;
            }
            const auto boolResult = [&](std::size_t index) {
                if (index == definitions_.size()) { return false; }
                std::string result_sort;
                H::Sort result_hir;
                return sort(definitions_[index].list[3], result_sort, result_hir, diagnostics)
                    && result_sort == "Bool";
            };
            const auto stateSignature = [&](std::size_t index) {
                if (!boolResult(index)
                    || definition_parameters_[index].size() != parameters_.size()) {
                    return false;
                }
                for (std::size_t i = 0; i < parameters_.size(); ++i) {
                    if (!H::sameSort(parameters_[i].hir_sort,
                                     definition_parameters_[index][i].hir_sort)) {
                        return false;
                    }
                }
                return true;
            };
            if (!stateSignature(pre) || !stateSignature(post) || !boolResult(trans)
                || definition_parameters_[trans].size() != 2 * parameters_.size()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "inv-constraint pre/post signatures must match the invariant and transition must take current and next state sorts");
                return false;
            }
            for (std::size_t i = 0; i < parameters_.size(); ++i) {
                if (!H::sameSort(parameters_[i].hir_sort,
                                 definition_parameters_[trans][i].hir_sort)
                    || !H::sameSort(parameters_[i].hir_sort,
                                    definition_parameters_[trans][i + parameters_.size()].hir_sort)) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "inv-constraint transition argument sorts do not match current/next state");
                    return false;
                }
            }
            const std::string& pre_name = command.list[2].atom;
            const std::string& trans_name = command.list[3].atom;
            const std::string& post_name = command.list[4].atom;
            constraints_.push_back(application("=>", {
                call(pre_name, current), call(function_name_, current)}));
            std::vector<std::string> both = current;
            both.insert(both.end(), next.begin(), next.end());
            constraints_.push_back(application("=>", {
                application("and", {call(function_name_, current), call(trans_name, both)}),
                call(function_name_, next)}));
            constraints_.push_back(application("=>", {
                call(function_name_, current), call(post_name, current)}));
        }
        return true;
    }

    bool instantiateHelperDefinitions(
        const std::string& prefix, const std::vector<Sexp>& candidates,
        Uir::Diagnostics& diagnostics) {
        candidate_helper_renames_.resize(candidates.size());
        candidate_helper_definitions_.resize(candidates.size());
        candidate_definition_global_indices_.resize(candidates.size());
        for (std::size_t i = 0; i < candidates.size(); ++i) {
            auto& renames = candidate_helper_renames_[i];
            for (std::size_t j = 0; j < definitions_.size(); ++j) {
                const std::string& name = definitions_[j].list[1].atom;
                const std::string target = definition_dependent_[j]
                    ? prefix + "helper_" + std::to_string(i) + "_" + name
                    : source_helper_targets_.at(name);
                renames.emplace(name, target);
                closure_definition_targets_[target] = j;
            }
            for (std::size_t j = 0; j < definitions_.size(); ++j) {
                if (!definition_dependent_[j]) { continue; }
                const Sexp& source_definition = definitions_[j];
                const std::string& source_name = source_definition.list[1].atom;
                std::set<std::string> shadowed;
                for (const Typed& parameter : definition_parameters_[j]) {
                    shadowed.insert(parameter.name);
                }
                bool substitution_ok = true;
                Sexp definition = source_definition;
                definition.list[1] = symbolSexp(renames.at(source_name));
                definition.list[4] = substituteFunction(
                    source_definition.list[4], candidates[i], substitution_ok,
                    renames, shadowed);
                if (!substitution_ok) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "a define-fun helper applies synth-fun '"
                                          + function_name_ + "' at the wrong arity");
                    return false;
                }
                candidate_helper_definitions_[i].push_back(std::move(definition));
            }
            if (!computeCandidateDefinitionGlobalClosure(i, diagnostics)) {
                return false;
            }
        }
        return true;
    }

    bool computeCandidateDefinitionGlobalClosure(
        std::size_t candidate_index, Uir::Diagnostics& diagnostics) {
        auto& closures = candidate_definition_global_indices_[candidate_index];
        closures = definition_global_indices_;
        std::map<std::string, std::size_t> target_indices;
        for (const auto& [name, index] : closure_definition_targets_) {
            target_indices.emplace(name, index);
        }
        const auto& instantiated = candidate_helper_definitions_[candidate_index];
        for (const Sexp& definition : instantiated) {
            const auto found = target_indices.find(definition.list[1].atom);
            if (found == target_indices.end()) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "generated SyGuS helper has no closure metadata");
                return false;
            }
            const std::size_t index = found->second;
            std::set<std::string> shadowed;
            for (const Typed& parameter : definition_parameters_[index]) {
                shadowed.insert(parameter.name);
            }
            std::set<std::size_t> globals;
            std::set<std::size_t> dependencies;
            collectClosureReferences(definition.list[4], shadowed, globals,
                                     dependencies, &target_indices);
            for (std::size_t dependency : dependencies) {
                if (dependency == index || dependency > index) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "candidate helper closure has a recursive or forward dependency");
                    return false;
                }
                globals.insert(closures[dependency].begin(),
                               closures[dependency].end());
            }
            closures[index].assign(globals.begin(), globals.end());
        }
        return true;
    }

    bool isBuiltinInSourceLogic(const std::string& name) const {
        // These are reserved by the SyGuS/SMT core grammar in every supported
        // logic, including the binder and let forms that are not represented
        // as ordinary operator applications in every parser path.
        static const std::set<std::string> core{
            "true", "false", "and", "or", "not", "=>", "xor", "=",
            "distinct", "ite", "forall", "exists", "let"};
        if (core.count(name) != 0) { return true; }
        if (logic_name_ == "SLIA") {
            static const std::set<std::string> strings{
                "str.++", "str.replace", "str.replace_all", "str.at", "str.substr",
                "str.len", "str.to_int", "str.from_int", "str.indexof",
                "str.contains", "str.prefixof", "str.suffixof",
                "str.to.int", "int.to.str"};
            if (strings.count(name) != 0) { return true; }
        }
        if (logic_name_ == "BV") {
            const SOMTParser::NODE_KIND kind = SOMTParser::getOperKind(name, false);
            const int value = static_cast<int>(kind);
            const int bv_first = static_cast<int>(SOMTParser::NODE_KIND::NT_BV_NOT);
            const int bv_last = static_cast<int>(SOMTParser::NODE_KIND::NT_BV_ROTATE_RIGHT);
            const int overflow_first = static_cast<int>(SOMTParser::NODE_KIND::NT_BV_NEGO);
            const int overflow_last = static_cast<int>(SOMTParser::NODE_KIND::NT_BV_SMODO);
            if ((value >= bv_first && value <= bv_last)
                || (value >= overflow_first && value <= overflow_last)) {
                return true;
            }
            // The overflow kinds are contiguous in NODE_KIND, but some legacy
            // spellings are printable kinds rather than entries in oper_key_map.
            // Recognize those names from the same enum range instead of
            // maintaining another operator-name whitelist.
            for (int current = overflow_first; current <= overflow_last; ++current) {
                if (SOMTParser::kindToString(
                        static_cast<SOMTParser::NODE_KIND>(current)) == name) {
                    return true;
                }
            }
            return false;
        }
        if (logic_name_ == "LIA" || logic_name_ == "NIA") {
            static const std::set<std::string> arithmetic{
                "+", "-", "*", "/", "div", "mod", "abs", "<", "<=", ">",
                ">=", "to_real", "to_int", "is_int"};
            return arithmetic.count(name) != 0;
        }
        if (logic_name_ == "ALL") {
            return SOMTParser::isBuiltinNameReservedAgainstUserFun(name);
        }
        // Unknown and solver-specific source logics are treated conservatively:
        // leave reserved names unaliased so target parsing can still reject them.
        return SOMTParser::isBuiltinNameReservedAgainstUserFun(name);
    }

    void initializeTargetHelperNames(const std::string& prefix) {
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            const std::string& name = definitions_[i].list[1].atom;
            // Some target solvers reserve these historical String aliases
            // even when the source logic permits them as user helper names.
            const bool target_string_alias = name == "int.to.str"
                                          || name == "str.to.int";
            if ((SOMTParser::isBuiltinNameReservedAgainstUserFun(name)
                 || target_string_alias)
                && !isBuiltinInSourceLogic(name)) {
                source_helper_targets_[name] =
                    prefix + "source_helper_" + std::to_string(i);
            } else {
                source_helper_targets_[name] = name;
            }
            closure_definition_targets_[source_helper_targets_.at(name)] = i;
        }
    }

    void initializeUniversalAliases(const std::string& prefix) {
        target_universal_variables_.clear();
        universal_aliases_.clear();
        std::set<std::size_t> captured;
        for (const auto& globals : definition_global_indices_) {
            captured.insert(globals.begin(), globals.end());
        }
        for (std::size_t i = 0; i < universal_variables_.size(); ++i) {
            Typed target = universal_variables_[i];
            // Freshen only globals captured by a helper. Uncaptured source
            // binders keep their previous names and cannot be captured at a
            // helper call site because they are not closure arguments.
            if (captured.count(i) != 0) {
                target.name = prefix + "universal_" + std::to_string(i);
                universal_aliases_.emplace(universal_variables_[i].name, target.name);
            }
            target_universal_variables_.push_back(std::move(target));
        }
    }

    void collectClosureReferences(const Sexp& expression,
                                  const std::set<std::string>& shadowed,
                                  std::set<std::size_t>& globals,
                                  std::set<std::size_t>& dependencies,
                                  const std::map<std::string, std::size_t>* helper_indices = nullptr) const {
        if (expression.isStringLiteral()) { return; }
        if (expression.isAtom()) {
            if (shadowed.count(expression.atom) != 0) { return; }
            const auto global = universal_indices_.find(expression.atom);
            if (global != universal_indices_.end()) { globals.insert(global->second); }
            const auto& indices = helper_indices ? *helper_indices : definition_indices_;
            const auto function = indices.find(expression.atom);
            if (function != indices.end()) {
                dependencies.insert(function->second);
            }
            return;
        }
        if (expression.list.empty()) { return; }
        if ((expression.head() == "forall" || expression.head() == "exists"
             || expression.head() == "lambda")
            && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            std::set<std::string> nested = shadowed;
            for (const Sexp& item : expression.list[1].list) {
                if (item.list.size() == 2 && item.list[0].isAtom()) {
                    nested.insert(item.list[0].atom);
                }
            }
            collectClosureReferences(expression.list[2], nested, globals, dependencies,
                                     helper_indices);
            return;
        }
        if (expression.head() == "let" && expression.list.size() == 3
            && !expression.list[1].isAtom()) {
            std::set<std::string> nested = shadowed;
            for (const Sexp& binding : expression.list[1].list) {
                if (binding.list.size() == 2 && binding.list[0].isAtom()) {
                    // SMT-LIB let initializers are simultaneous and remain in
                    // the outer scope; only the body sees the new bindings.
                    collectClosureReferences(binding.list[1], shadowed,
                                             globals, dependencies, helper_indices);
                    nested.insert(binding.list[0].atom);
                }
            }
            collectClosureReferences(expression.list[2], nested, globals, dependencies,
                                     helper_indices);
            return;
        }
        const bool function_head = expression.list[0].isAtom()
            && !expression.list[0].isStringLiteral()
            && shadowed.count(expression.list[0].atom) == 0;
        if (function_head) {
            const auto& indices = helper_indices ? *helper_indices : definition_indices_;
            const auto dependency = indices.find(expression.list[0].atom);
            if (dependency != indices.end()) {
                dependencies.insert(dependency->second);
            }
        }
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            collectClosureReferences(expression.list[i], shadowed, globals, dependencies,
                                     helper_indices);
        }
    }

    bool computeDefinitionGlobalClosure(Uir::Diagnostics& diagnostics) {
        universal_indices_.clear();
        for (std::size_t i = 0; i < universal_variables_.size(); ++i) {
            universal_indices_.emplace(universal_variables_[i].name, i);
        }
        definition_indices_.clear();
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            definition_indices_.emplace(definitions_[i].list[1].atom, i);
        }
        definition_global_indices_.assign(definitions_.size(), {});
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            std::set<std::string> shadowed;
            for (const Typed& parameter : definition_parameters_[i]) {
                shadowed.insert(parameter.name);
            }
            std::set<std::size_t> globals;
            std::set<std::size_t> dependencies;
            collectClosureReferences(definitions_[i].list[4], shadowed,
                                     globals, dependencies);
            for (std::size_t dependency : dependencies) {
                if (dependency == i || dependency > i) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "define-fun closure has a recursive or forward dependency");
                    return false;
                }
                globals.insert(definition_global_indices_[dependency].begin(),
                               definition_global_indices_[dependency].end());
            }
            definition_global_indices_[i].assign(globals.begin(), globals.end());
        }
        return true;
    }

    Sexp closeExpression(const Sexp& expression,
                         const std::set<std::string>& shadowed) const {
        if (expression.isStringLiteral()) { return expression; }
        const auto& globals_by_definition = active_candidate_definition_globals_
            ? *active_candidate_definition_globals_ : definition_global_indices_;
        if (expression.isAtom()) {
            if (shadowed.count(expression.atom) != 0) { return expression; }
            const auto global = universal_aliases_.find(expression.atom);
            if (global != universal_aliases_.end()) { return symbolSexp(global->second); }
            const auto helper = closure_definition_targets_.find(expression.atom);
            if (helper != closure_definition_targets_.end()
                && !globals_by_definition[helper->second].empty()) {
                Sexp call;
                call.list.push_back(expression);
                for (std::size_t index : globals_by_definition[helper->second]) {
                    call.list.push_back(symbolSexp(target_universal_variables_[index].name));
                }
                return call;
            }
            return expression;
        }
        if (expression.list.empty()) { return expression; }
        if ((expression.head() == "forall" || expression.head() == "exists"
             || expression.head() == "lambda")
            && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            Sexp result;
            result.list = {expression.list[0], expression.list[1]};
            std::set<std::string> nested = shadowed;
            for (const Sexp& item : expression.list[1].list) {
                if (item.list.size() == 2 && item.list[0].isAtom()) {
                    nested.insert(item.list[0].atom);
                }
            }
            result.list.push_back(closeExpression(expression.list[2], nested));
            return result;
        }
        if (expression.head() == "let" && expression.list.size() == 3
            && !expression.list[1].isAtom()) {
            Sexp result;
            result.list.push_back(expression.list[0]);
            Sexp bindings;
            std::set<std::string> nested = shadowed;
            for (const Sexp& binding : expression.list[1].list) {
                if (binding.list.size() == 2 && binding.list[0].isAtom()) {
                    bindings.list.push_back(form({binding.list[0],
                        closeExpression(binding.list[1], shadowed)}));
                    nested.insert(binding.list[0].atom);
                } else {
                    bindings.list.push_back(binding);
                }
            }
            result.list.push_back(std::move(bindings));
            result.list.push_back(closeExpression(expression.list[2], nested));
            return result;
        }
        Sexp result;
        const bool helper_call = expression.list[0].isAtom()
            && !expression.list[0].isStringLiteral()
            && shadowed.count(expression.list[0].atom) == 0
            && closure_definition_targets_.count(expression.list[0].atom) != 0;
        for (std::size_t i = 0; i < expression.list.size(); ++i) {
            if (i == 0) { result.list.push_back(expression.list[i]); }
            else { result.list.push_back(closeExpression(expression.list[i], shadowed)); }
        }
        if (helper_call) {
            const std::size_t index = closure_definition_targets_.at(expression.list[0].atom);
            for (std::size_t global : globals_by_definition[index]) {
                result.list.push_back(symbolSexp(target_universal_variables_[global].name));
            }
        }
        return result;
    }

    Sexp renameEvaluationParameters(
        const Sexp& expression,
        const std::map<std::string, std::string>& aliases,
        const std::set<std::string>& shadowed) const {
        if (expression.isStringLiteral()) { return expression; }
        if (expression.isAtom()) {
            if (shadowed.count(expression.atom) != 0) { return expression; }
            const auto found = aliases.find(expression.atom);
            return found == aliases.end() ? expression : symbolSexp(found->second);
        }
        if (expression.list.empty()) { return expression; }
        const std::string& head = expression.list.front().atom;
        const bool special_head = expression.list.front().isAtom()
                               && !expression.list.front().isQuotedSymbol()
                               && !expression.list.front().isStringLiteral();
        if (special_head && (head == "forall" || head == "exists" || head == "lambda")
            && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            Sexp result;
            result.list = {expression.list[0], expression.list[1]};
            std::set<std::string> nested = shadowed;
            for (const Sexp& binder_entry : expression.list[1].list) {
                if (binder_entry.list.size() == 2 && binder_entry.list[0].isAtom()) {
                    nested.insert(binder_entry.list[0].atom);
                }
            }
            result.list.push_back(renameEvaluationParameters(
                expression.list[2], aliases, nested));
            return result;
        }
        if (special_head && head == "let" && expression.list.size() == 3
            && !expression.list[1].isAtom()) {
            Sexp result;
            result.list.push_back(expression.list[0]);
            Sexp bindings;
            std::set<std::string> nested = shadowed;
            for (const Sexp& binding : expression.list[1].list) {
                if (binding.list.size() == 2 && binding.list[0].isAtom()) {
                    bindings.list.push_back(form({binding.list[0],
                        renameEvaluationParameters(binding.list[1], aliases, shadowed)}));
                    nested.insert(binding.list[0].atom);
                } else {
                    bindings.list.push_back(binding);
                }
            }
            result.list.push_back(std::move(bindings));
            result.list.push_back(renameEvaluationParameters(
                expression.list[2], aliases, nested));
            return result;
        }
        Sexp result;
        result.list.reserve(expression.list.size());
        result.list.push_back(expression.list.front());
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            result.list.push_back(renameEvaluationParameters(
                expression.list[i], aliases, shadowed));
        }
        return result;
    }

    void appendClosureParameters(Sexp& definition, std::size_t index) const {
        const auto& globals_by_definition = active_candidate_definition_globals_
            ? *active_candidate_definition_globals_ : definition_global_indices_;
        for (std::size_t global : globals_by_definition[index]) {
            const Typed& variable = target_universal_variables_[global];
            definition.list[2].list.push_back(
                form({symbolSexp(variable.name), canonicalSort(variable.hir_sort)}));
        }
    }

    bool readCommands(Uir::Diagnostics& diagnostics) {
        bool saw_synth = false;
        bool saw_check = false;
        std::set<std::string> universal_names;
        for (command_index_ = 0; command_index_ < commands_.size(); ++command_index_) {
            const Sexp& command = commands_[command_index_];
            const std::string head = command.head();
            if (head == "set-logic") {
                if (command.list.size() != 2 || !command.list[1].isAtom()
                    || !logic_name_.empty()) {
                    diagnostics.error(ErrorCode::E_PARSE, "malformed SyGuS set-logic");
                    return false;
                }
                logic_name_ = command.list[1].atom;
            } else if (head == "set-option" || head == "set-info") {
                // Output and metadata commands do not change the synthesis relation.
            } else if (head == "define-fun") {
                if (command.list.size() != 5 || !command.list[1].isAtom()
                    || !simpleSymbol(command.list[1])) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed SyGuS define-fun command");
                    return false;
                }
                const std::string& name = command.list[1].atom;
                if (isBuiltinInSourceLogic(name)) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "define-fun name '" + name
                                          + "' is reserved by source logic "
                                          + logic_name_);
                    return false;
                }
                if (universal_names.count(name) != 0 || synth_names_.count(name) != 0
                    || !definition_names_.insert(name).second) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "duplicate SyGuS function definition '" + name + "'");
                    return false;
                }
                std::vector<Typed> parameters;
                std::string result_sort;
                H::Sort result_hir;
                if (!typedBinder(command.list[2], "define-fun parameters", parameters,
                                 diagnostics)
                    || !sort(command.list[3], result_sort, result_hir, diagnostics)) {
                    return false;
                }
                definitions_.push_back(command);
                // Official older SyGuS corpora spell BV sorts as (BitVec W).
                // Every emitted SMT binder/result must use indexed SMT syntax.
                auto& definition = definitions_.back();
                definition.list[2].list.clear();
                for (const Typed& parameter : parameters) {
                    definition.list[2].list.push_back(
                        form({symbolSexp(parameter.name), canonicalSort(parameter.hir_sort)}));
                }
                definition.list[3] = canonicalSort(result_hir);
                definition_parameters_.push_back(std::move(parameters));
                definition_after_synth_.push_back(saw_synth);
                definition_command_indices_.push_back(command_index_);
                definition_visible_synths_.push_back(synth_names_);
                definition_visible_universals_.push_back(universal_names);
            } else if (head == "synth-fun") {
                if (invariant_mode_) {
                    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                      "synth-fun cannot be combined with synth-inv");
                    return false;
                }
                if ((command.list.size() != 4 && command.list.size() != 5
                     && command.list.size() != 6)
                    || !command.list[1].isAtom()
                    || !simpleSymbol(command.list[1])) {
                    diagnostics.error(
                        ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "malformed or unsupported synth-fun command");
                    return false;
                }
                SynthFunction function;
                function.name = command.list[1].atom;
                function.command_index = command_index_;
                if (isBuiltinInSourceLogic(function.name)) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "synth-fun name '" + function.name
                                          + "' is reserved by source logic "
                                          + logic_name_);
                    return false;
                }
                if (universal_names.count(function.name) != 0
                    || definition_names_.count(function.name) != 0
                    || !synth_names_.insert(function.name).second) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "synth-fun duplicates a prior define-fun '"
                                          + function.name + "'");
                    return false;
                }
                if (!typedBinder(command.list[2], "synth-fun parameters", function.parameters,
                                 diagnostics)
                    || !sort(command.list[3], function.return_sort,
                             function.return_hir_sort, diagnostics)) {
                    return false;
                }
                if (command.list.size() == 4) {
                    function.default_grammar_requested = true;
                } else if (command.list.size() == 5) {
                    // SyGuS-IF 1.0 puts all grouped nonterminal rules in one
                    // grammar argument. Normalize it to the 2.0
                    // predeclaration + grouped-rule representation so both
                    // versions share the same sort and production checks.
                    const Sexp& legacy_groups = command.list[4];
                    if (legacy_groups.isAtom() || legacy_groups.list.empty()) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "malformed legacy SyGuS grammar rule list");
                        return false;
                    }
                    std::vector<Sexp> declarations;
                    for (const Sexp& group : legacy_groups.list) {
                        if (group.list.size() != 3 || !group.list[0].isAtom()) {
                            diagnostics.error(
                                ErrorCode::E_PARSE,
                                "malformed legacy grouped grammar rule; expected "
                                "(Nonterminal Sort (Rules...))");
                            return false;
                        }
                        declarations.push_back(form({group.list[0], group.list[1]}));
                    }
                    function.grammar_declarations = form(declarations);
                    function.grammar_rules = legacy_groups;
                } else {
                    function.grammar_declarations = command.list[4];
                    function.grammar_rules = command.list[5];
                }
                synth_functions_.push_back(std::move(function));
                saw_synth = true;
            } else if (head == "synth-inv") {
                if (saw_synth || (command.list.size() != 3 && command.list.size() != 4
                                  && command.list.size() != 5)
                    || !command.list[1].isAtom() || !simpleSymbol(command.list[1])) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed or duplicate synth-inv command");
                    return false;
                }
                // Invariant declarations synthesize a Bool predicate. Normalize
                // them to the same bounded grammar path used by synth-fun.
                invariant_mode_ = true;
                function_name_ = command.list[1].atom;
                if (isBuiltinInSourceLogic(function_name_)) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "synth-inv name '" + function_name_
                                          + "' is reserved by source logic "
                                          + logic_name_);
                    return false;
                }
                if (universal_names.count(function_name_) != 0
                    || definition_names_.count(function_name_) != 0) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "synth-inv duplicates a prior define-fun '"
                                          + function_name_ + "'");
                    return false;
                }
                if (!typedBinder(command.list[2], "synth-inv parameters", parameters_,
                                 diagnostics)) { return false; }
                return_sort_ = "Bool";
                return_hir_sort_ = H::Sort::boolean();
                if (command.list.size() == 3) { default_grammar_requested_ = true; }
                else if (command.list.size() == 4) {
                    // The invariant extension's optional grammar is one grouped
                    // grammar argument, as in the legacy SyGuS-IF syntax.
                    const Sexp& groups = command.list[3];
                    if (groups.isAtom() || groups.list.empty()) {
                        diagnostics.error(ErrorCode::E_PARSE, "malformed synth-inv grammar");
                        return false;
                    }
                    std::vector<Sexp> declarations;
                    for (const Sexp& group : groups.list) {
                        if (group.list.size() != 3 || !group.list[0].isAtom()) {
                            diagnostics.error(ErrorCode::E_PARSE,
                                              "malformed synth-inv grammar group");
                            return false;
                        }
                        declarations.push_back(form({group.list[0], group.list[1]}));
                    }
                    grammar_declarations_ = form(declarations);
                    grammar_rules_ = groups;
                } else {
                    grammar_declarations_ = command.list[3];
                    grammar_rules_ = command.list[4];
                }
                SynthFunction function;
                function.name = function_name_;
                function.parameters = parameters_;
                function.return_sort = return_sort_;
                function.return_hir_sort = return_hir_sort_;
                function.default_grammar_requested = default_grammar_requested_;
                function.invariant = true;
                function.command_index = command_index_;
                function.grammar_declarations = grammar_declarations_;
                function.grammar_rules = grammar_rules_;
                synth_names_.insert(function.name);
                synth_functions_.push_back(std::move(function));
                saw_synth = true;
            } else if (head == "declare-var") {
                if (command.list.size() != 3 || !command.list[1].isAtom()
                    || !simpleSymbol(command.list[1])) {
                    diagnostics.error(ErrorCode::E_PARSE, "malformed declare-var command");
                    return false;
                }
                Typed variable;
                variable.name = command.list[1].atom;
                if (synth_names_.count(variable.name) != 0
                    || definition_names_.count(variable.name) != 0
                    || !universal_names.insert(variable.name).second) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "duplicate declare-var '" + variable.name + "'");
                    return false;
                }
                if (!sort(command.list[2], variable.sort, variable.hir_sort, diagnostics)) {
                    return false;
                }
                universal_variables_.push_back(std::move(variable));
            } else if (head == "declare-primed-var") {
                if (command.list.size() != 3 || !command.list[1].isAtom()
                    || !simpleSymbol(command.list[1])) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed declare-primed-var command");
                    return false;
                }
                for (const std::string& name : {command.list[1].atom,
                                                command.list[1].atom + "!"}) {
                    if (synth_names_.count(name) != 0
                        || definition_names_.count(name) != 0) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "primed variable '" + name
                                              + "' duplicates a function symbol");
                        return false;
                    }
                    if (!universal_names.insert(name).second) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "duplicate declared variable '" + name + "'");
                        return false;
                    }
                    Typed variable;
                    variable.name = name;
                    if (!sort(command.list[2], variable.sort, variable.hir_sort, diagnostics)) {
                        return false;
                    }
                    universal_variables_.push_back(std::move(variable));
                }
            } else if (head == "constraint") {
                if (command.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE, "constraint takes one term");
                    return false;
                }
                constraints_.push_back(command.list[1]);
            } else if (head == "check-synth") {
                if (command.list.size() != 1 || saw_check) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "exactly one nullary check-synth is required");
                    return false;
                }
                saw_check = true;
            } else if (head == "inv-constraint") {
                if (!saw_synth || saw_check || command.list.size() != 5) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "inv-constraint requires a prior synth-inv and invariant, pre, trans, post names");
                    return false;
                }
                for (std::size_t i = 1; i < 5; ++i) {
                    if (!command.list[i].isAtom() || !simpleSymbol(command.list[i])) {
                        diagnostics.error(ErrorCode::E_PARSE,
                                          "inv-constraint arguments must be function names");
                        return false;
                    }
                }
                if (synth_functions_.size() != 1
                    || command.list[1].atom != synth_functions_.front().name
                    || definition_names_.count(command.list[2].atom) == 0
                    || definition_names_.count(command.list[3].atom) == 0
                    || definition_names_.count(command.list[4].atom) == 0) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "inv-constraint must name its synth-inv and previously declared pre/trans/post functions");
                    return false;
                }
                invariant_constraints_.push_back(command);
            } else if (head == "assume" || head.rfind("oracle", 0) == 0) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "SyGuS command '" + head
                                      + "' needs invariant/oracle synthesis semantics");
                return false;
            } else {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unsupported SyGuS command '" + head + "'");
                return false;
            }
        }
        if (!saw_synth || !saw_check) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "SyGuS input requires synth-fun/synth-inv and check-synth");
            return false;
        }
        if (!normalizeTypedLetSources(diagnostics)
            || !validateDefinitions(diagnostics)
            || !elaborateInvariantConstraints(diagnostics)) { return false; }
        if (invariant_mode_ && synth_functions_.size() != 1) {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "joint synth-fun/synth-inv products are unsupported");
            return false;
        }
        return true;
    }

    static Sexp atom(std::string value) {
        Sexp result;
        result.atom = std::move(value);
        return result;
    }

    static Sexp form(std::initializer_list<Sexp> children) {
        Sexp result;
        result.list.assign(children.begin(), children.end());
        return result;
    }

    static Sexp form(const std::vector<Sexp>& children) {
        Sexp result;
        result.list = children;
        return result;
    }

    static Sexp application(std::string op, std::initializer_list<Sexp> arguments) {
        Sexp result;
        result.list.push_back(atom(std::move(op)));
        result.list.insert(result.list.end(), arguments.begin(), arguments.end());
        return result;
    }

    bool prepareUnboundedAstGrammar(std::size_t function_index,
                                    const std::string& prefix,
                                    Uir::Diagnostics& diagnostics) {
        SynthFunction& function = synth_functions_[function_index];
        function_name_ = function.name;
        parameters_ = function.parameters;
        return_sort_ = function.return_sort;
        return_hir_sort_ = function.return_hir_sort;
        active_function_command_index_ = function.command_index;
        default_grammar_requested_ = function.default_grammar_requested;
        grammar_declarations_ = function.grammar_declarations;
        grammar_rules_ = function.grammar_rules;
        nonterminals_.clear();
        nonterminal_indices_.clear();
        if (!buildDefaultGrammar(diagnostics) || !readGrammar(diagnostics)) return false;

        // A one-rule root `(Constant Sort)` already denotes every value of
        // that result sort. Represent it directly by a target value instead of
        // building an ADT and universally quantified evaluator/renderer. Besides
        // reducing the solver formula, the model value is itself an exact source
        // literal for Int/Bool/BitVec/String, so no recursive decimal or String
        // escaping axioms are needed for witness extraction.
        if (nonterminals_.size() == 1
            && nonterminals_.front().rules.size() == 1) {
            const Sexp& only_rule = nonterminals_.front().rules.front();
            if (only_rule.list.size() == 2 && only_rule.head() == "Constant") {
                std::string constant_sort;
                H::Sort constant_hir_sort;
                if (!sort(only_rule.list[1], constant_sort, constant_hir_sort,
                          diagnostics)) {
                    return false;
                }
                if (H::sameSort(constant_hir_sort, return_hir_sort_)) {
                    const std::string target = prefix + "witness_value_"
                                             + std::to_string(function_index);
                    function.unbounded_direct_constant = true;
                    function.witness_value_target = target;
                    std::ostringstream direct;
                    direct << "(declare-const " << target << ' '
                           << printSexp(canonicalSort(return_hir_sort_)) << ")\n";
                    unbounded_prelude_ = direct.str();
                    unbounded_candidate_ = renderSymbol(target);
                    unbounded_source_term_placeholder_ = prefix
                        + "source_term_placeholder_" + std::to_string(function_index);
                    unbounded_source_term_symbol_ = prefix + "source_witness_"
                        + std::to_string(function_index);
                    return true;
                }
            }
        }

        std::vector<AstGrammarNonterminal> ast(nonterminals_.size());
        unbounded_eval_parameter_names_.clear();
        for (std::size_t i = 0; i < parameters_.size(); ++i) {
            unbounded_eval_parameter_names_.push_back(prefix + "eval_arg_"
                + std::to_string(function_index) + "_" + std::to_string(i));
        }
        std::size_t constructor_index = 0;
        // Nested production fragments use temporary vectors. A local child
        // count restarts in each fragment and can alias sibling occurrences.
        // Allocate each AST child once from the function-wide field namespace.
        std::size_t child_index = 0;
        for (std::size_t ni = 0; ni < nonterminals_.size(); ++ni) {
            ast[ni].name = nonterminals_[ni].name;
            ast[ni].sort = nonterminals_[ni].sort;
            ast[ni].ast_sort = prefix + "ast_" + std::to_string(function_index)
                             + "_" + std::to_string(ni);
            ast[ni].eval_name = prefix + "eval_" + std::to_string(function_index)
                              + "_" + std::to_string(ni);
            ast[ni].render_name = prefix + "render_" + std::to_string(function_index)
                                + "_" + std::to_string(ni);
        }
        std::map<std::string, std::size_t> ast_indices = nonterminal_indices_;

        const auto makeProduction = [&](const Sexp& rule,
                                        AstGrammarProduction& production,
                                        const auto& self) -> bool {
            if (rule.isAtom()) {
                if (!rule.isStringLiteral()) {
                    const auto child = ast_indices.find(rule.atom);
                    if (child != ast_indices.end()) {
                        const std::size_t occurrence = child_index++;
                        const std::string marker = prefix + "child_"
                            + std::to_string(function_index) + "_"
                            + std::to_string(occurrence);
                        production.child_nonterminals.push_back(rule.atom);
                        production.child_markers.push_back(marker);
                        production.child_selectors.push_back(prefix + "field_"
                            + std::to_string(function_index) + "_"
                            + std::to_string(occurrence));
                        production.source_template = atom(marker);
                        return true;
                    }
                }
                production.source_template = rule;
                if (!rule.quoted_symbol && legacyNegativeInteger(rule.atom)) {
                    production.source_template = form({atom("-"), atom(rule.atom.substr(1))});
                }
                return true;
            }
            if (rule.list.empty()) {
                production.source_template = rule;
                return true;
            }
            if (rule.head() == "Constant") {
                if (rule.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE, "malformed (Constant Sort) grammar term");
                    return false;
                }
                std::string sort_text;
                H::Sort value_sort;
                if (!sort(rule.list[1], sort_text, value_sort, diagnostics)) return false;
                if (value_sort.kind != H::SortKind::BOOL
                    && value_sort.kind != H::SortKind::INT
                    && value_sort.kind != H::SortKind::BITVEC
                    && value_sort.kind != H::SortKind::STRING) {
                    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                        "unbounded AST renderer supports Constant Bool, Int, BitVec, and String; "
                        "other constant sorts need an exact source-literal renderer");
                    return false;
                }
                // A literal may occur below the root of a production, for
                // example `(and (Constant Bool) Start)`. Nested nodes are
                // first collected in a temporary AstGrammarProduction, so a
                // per-vector index would restart at zero and collide with a
                // sibling literal. Reserve from the same function-wide
                // constructor namespace instead: every marker and selector
                // then has a stable, unique SMT declaration name.
                const std::size_t value_index = constructor_index++;
                const std::string marker = prefix + "grammar_literal_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(constructor_index) + "_" + std::to_string(value_index);
                production.literal_sorts.push_back(sort_text);
                production.literal_bit_widths.push_back(
                    value_sort.kind == H::SortKind::BITVEC ? value_sort.width : 0);
                production.literal_markers.push_back(marker);
                production.literal_selectors.push_back(prefix + "value_field_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(constructor_index) + "_" + std::to_string(value_index));
                production.source_template = atom(marker);
                return true;
            }
            if (rule.head() == "Variable") {
                if (rule.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed (Variable Sort) grammar term");
                    return false;
                }
                std::string variable_sort;
                H::Sort variable_hir_sort;
                if (!sort(rule.list[1], variable_sort, variable_hir_sort, diagnostics)) {
                    return false;
                }
                const std::size_t variable_id = constructor_index++;
                AstGrammarNonterminal variable_nt;
                variable_nt.name = prefix + "variable_choice_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(variable_id);
                variable_nt.sort = variable_sort;
                variable_nt.ast_sort = prefix + "ast_variable_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(variable_id);
                variable_nt.eval_name = prefix + "eval_variable_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(variable_id);
                variable_nt.render_name = prefix + "render_variable_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(variable_id);
                for (const Typed& parameter : parameters_) {
                    if (!H::sameSort(parameter.hir_sort, variable_hir_sort)) continue;
                    AstGrammarProduction variable;
                    variable.constructor = prefix + "ctor_"
                        + std::to_string(function_index) + "_"
                        + std::to_string(constructor_index++);
                    variable.source_template = symbolSexp(parameter.name);
                    variable_nt.productions.push_back(std::move(variable));
                }
                const std::size_t variable_index = ast.size();
                ast_indices.emplace(variable_nt.name, variable_index);
                ast.push_back(std::move(variable_nt));
                const std::size_t occurrence = child_index++;
                const std::string marker = prefix + "child_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(occurrence);
                production.child_nonterminals.push_back(ast[variable_index].name);
                production.child_markers.push_back(marker);
                production.child_selectors.push_back(prefix + "field_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(occurrence));
                production.source_template = atom(marker);
                return true;
            }
            Sexp rewritten;
            rewritten.list.reserve(rule.list.size());
            for (const Sexp& child : rule.list) {
                if (child.isAtom() && !child.isStringLiteral()
                    && ast_indices.find(child.atom) != ast_indices.end()) {
                    const std::size_t occurrence = child_index++;
                    const std::string marker = prefix + "child_"
                        + std::to_string(function_index) + "_"
                        + std::to_string(occurrence);
                    production.child_nonterminals.push_back(child.atom);
                    production.child_markers.push_back(marker);
                    production.child_selectors.push_back(prefix + "field_"
                        + std::to_string(function_index) + "_"
                        + std::to_string(occurrence));
                    rewritten.list.push_back(atom(marker));
                } else {
                    AstGrammarProduction sub;
                    if (!self(child, sub, self)) return false;
                    // Recursive descent here only follows the finite source
                    // production's S-expression; recursive grammar edges are
                    // captured as AST fields and never descend during build.
                    for (std::size_t i = 0; i < sub.child_markers.size(); ++i) {
                        production.child_nonterminals.push_back(sub.child_nonterminals[i]);
                        production.child_markers.push_back(sub.child_markers[i]);
                        production.child_selectors.push_back(sub.child_selectors[i]);
                    }
                    // The recursive production renderer needs the complete
                    // metadata for every nested Constant leaf as well as its
                    // child AST fields. Without this propagation the template
                    // retained a marker atom that had no selector and became
                    // a free, undeclared SMT symbol in the evaluator.
                    production.literal_sorts.insert(
                        production.literal_sorts.end(), sub.literal_sorts.begin(),
                        sub.literal_sorts.end());
                    production.literal_selectors.insert(
                        production.literal_selectors.end(), sub.literal_selectors.begin(),
                        sub.literal_selectors.end());
                    production.literal_markers.insert(
                        production.literal_markers.end(), sub.literal_markers.begin(),
                        sub.literal_markers.end());
                    production.literal_bit_widths.insert(
                        production.literal_bit_widths.end(),
                        sub.literal_bit_widths.begin(), sub.literal_bit_widths.end());
                    rewritten.list.push_back(std::move(sub.source_template));
                }
            }
            production.source_template = std::move(rewritten);
            return true;
        };

        for (std::size_t ni = 0; ni < nonterminals_.size(); ++ni) {
            for (const Sexp& rule : nonterminals_[ni].rules) {
                if (rule.head() == "Variable") {
                    if (rule.list.size() != 2) {
                        diagnostics.error(ErrorCode::E_PARSE, "malformed (Variable Sort) grammar term");
                        return false;
                    }
                    std::string wanted_text;
                    H::Sort wanted;
                    if (!sort(rule.list[1], wanted_text, wanted, diagnostics)) return false;
                    for (const Typed& parameter : parameters_) {
                        if (!H::sameSort(parameter.hir_sort, wanted)) continue;
                        AstGrammarProduction production;
                        production.constructor = prefix + "ctor_"
                            + std::to_string(function_index) + "_"
                            + std::to_string(constructor_index++);
                        production.source_template = atom(renderSymbol(parameter.name));
                        ast[ni].productions.push_back(std::move(production));
                    }
                    continue;
                }
                if (rule.head() == "Constant" && rule.list.size() == 2) {
                    std::string constant_sort;
                    H::Sort constant_hir;
                    if (!sort(rule.list[1], constant_sort, constant_hir, diagnostics)) return false;
                    if (constant_hir.kind == H::SortKind::BOOL) {
                        for (const std::string& literal : {std::string("false"), std::string("true")}) {
                            AstGrammarProduction production;
                            production.constructor = prefix + "ctor_"
                                + std::to_string(function_index) + "_"
                                + std::to_string(constructor_index++);
                            production.source_template = atom(literal);
                            ast[ni].productions.push_back(std::move(production));
                        }
                        continue;
                    }
                }
                AstGrammarProduction production;
                production.constructor = prefix + "ctor_" + std::to_string(function_index)
                                       + "_" + std::to_string(constructor_index++);
                if (!makeProduction(rule, production, makeProduction)) return false;
                ast[ni].productions.push_back(std::move(production));
            }
        }

        // Compute the least finite-tree productivity fixed point. Recursive
        // productions without a terminating base (A ::= A) do not denote an
        // AST value in an inductive datatype and must not be made productive
        // merely because the target datatype sort is non-empty.
        std::vector<bool> productive(ast.size(), false);
        bool changed = true;
        while (changed) {
            changed = false;
            for (std::size_t ni = 0; ni < ast.size(); ++ni) {
                if (productive[ni]) continue;
                for (const auto& production : ast[ni].productions) {
                    const bool children_productive = std::all_of(
                        production.child_nonterminals.begin(),
                        production.child_nonterminals.end(), [&](const std::string& child) {
                            const auto found = ast_indices.find(child);
                            return found != ast_indices.end() && productive[found->second];
                        });
                    if (children_productive) { productive[ni] = true; changed = true; break; }
                }
            }
        }
        const std::size_t root_nt = 0;
        if (!productive[root_nt]) {
            // The grammar language is empty, so synthesis is unsatisfiable.
            // Keep a harmless singleton datatype so the common projection
            // contract remains well-formed; the explicit false assertion makes
            // every target model impossible, independent of its placeholder
            // evaluator and renderer values.
            const std::string ast_sort = prefix + "ast_empty_"
                                       + std::to_string(function_index);
            const std::string constructor = prefix + "ctor_empty_"
                                          + std::to_string(function_index);
            const std::string ast_parameter = prefix + "ast_value_"
                                            + std::to_string(function_index);
            std::string default_term;
            switch (function.return_hir_sort.kind) {
            case H::SortKind::BOOL: default_term = "false"; break;
            case H::SortKind::INT: default_term = "0"; break;
            case H::SortKind::STRING: default_term = "\"\""; break;
            case H::SortKind::BITVEC:
                default_term = "(_ bv0 "
                             + std::to_string(function.return_hir_sort.width) + ")";
                break;
            default:
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unbounded empty grammar has an unsupported result sort");
                return false;
            }
            std::ostringstream empty_encoding;
            empty_encoding << "(declare-datatypes ((" << ast_sort
                           << " 0)) (((" << constructor << "))))\n"
                           << "(define-fun " << prefix << "eval_empty_"
                           << function_index << " ((" << ast_parameter << ' '
                           << ast_sort << ')';
            for (std::size_t i = 0; i < parameters_.size(); ++i) {
                empty_encoding << " (" << unbounded_eval_parameter_names_[i] << ' '
                               << parameters_[i].sort << ')';
            }
            for (const Typed& global : target_universal_variables_) {
                empty_encoding << " (" << renderSymbol(global.name) << ' '
                               << printSexp(canonicalSort(global.hir_sort)) << ')';
            }
            empty_encoding << ") " << function.return_sort << ' ' << default_term
                           << ")\n"
                           << "(define-fun " << prefix << "render_empty_" << function_index << " (("
                           << ast_parameter << ' ' << ast_sort << ")) String "
                           << quoteSmtString(default_term) << ")\n"
                           << "(declare-const " << prefix << "ast_root_empty_"
                           << function_index << ' ' << ast_sort << ")\n"
                           << "(declare-const " << prefix << "witness_text_empty_"
                           << function_index << " String)\n"
                           << "(assert (= " << prefix << "witness_text_empty_"
                           << function_index << " (" << prefix << "render_empty_" << function_index << " "
                           << prefix << "ast_root_empty_" << function_index << ")))\n"
                           << "(assert false)\n";
            unbounded_prelude_ = empty_encoding.str();
            function.ast_root_target = prefix + "ast_root_empty_"
                                     + std::to_string(function_index);
            function.witness_text_target = prefix + "witness_text_empty_"
                                        + std::to_string(function_index);
            unbounded_source_term_placeholder_ = prefix + "source_term_placeholder_"
                                           + std::to_string(function_index);
            unbounded_source_term_symbol_ = prefix + "source_witness_"
                                          + std::to_string(function_index);
            unbounded_candidate_ = "(" + prefix + "eval_empty_"
                                 + std::to_string(function_index) + " "
                                 + function.ast_root_target;
            for (const Typed& parameter : parameters_) {
                unbounded_candidate_ += " " + renderSymbol(parameter.name);
            }
            for (const Typed& global : target_universal_variables_) {
                unbounded_candidate_ += " " + renderSymbol(global.name);
            }
            unbounded_candidate_ += ")";
            function.unbounded_prelude = unbounded_prelude_;
            function.unbounded_source_term_placeholder =
                unbounded_source_term_placeholder_;
            function.unbounded_source_term_symbol = unbounded_source_term_symbol_;
            return true;
        }
        for (std::size_t ni = 0; ni < ast.size(); ++ni) {
            auto& productions = ast[ni].productions;
            productions.erase(std::remove_if(productions.begin(), productions.end(),
                [&](const AstGrammarProduction& production) {
                    return std::any_of(production.child_nonterminals.begin(),
                        production.child_nonterminals.end(), [&](const std::string& child) {
                            return !productive[ast_indices.at(child)];
                        });
                }), productions.end());
        }

        std::vector<bool> reachable(ast.size(), false);
        std::vector<std::size_t> pending{root_nt};
        while (!pending.empty()) {
            const std::size_t current = pending.back(); pending.pop_back();
            if (reachable[current]) continue;
            reachable[current] = true;
            for (const auto& production : ast[current].productions) {
                for (const auto& child : production.child_nonterminals) {
                    pending.push_back(ast_indices.at(child));
                }
            }
        }

        std::vector<AstGrammarNonterminal> live;
        for (std::size_t ni = 0; ni < ast.size(); ++ni) {
            if (reachable[ni]) { live.push_back(std::move(ast[ni])); }
        }
        std::map<std::string, std::size_t> live_index;
        for (std::size_t i = 0; i < live.size(); ++i) live_index.emplace(live[i].name, i);
        const auto childSort = [&](const std::string& name) -> const std::string& {
            return live.at(live_index.at(name)).ast_sort;
        };

        std::ostringstream generated;
        const std::string ast_parameter = prefix + "ast_value_"
                                        + std::to_string(function_index);
        generated << "(declare-datatypes (";
        for (std::size_t i = 0; i < live.size(); ++i) {
            if (i) generated << ' ';
            generated << '(' << live[i].ast_sort << " 0)";
        }
        generated << ") (";
        for (std::size_t i = 0; i < live.size(); ++i) {
            if (i) generated << ' ';
            generated << '(';
                for (std::size_t pi = 0; pi < live[i].productions.size(); ++pi) {
                if (pi) generated << ' ';
                const auto& production = live[i].productions[pi];
                generated << '(' << production.constructor;
                for (std::size_t ci = 0; ci < production.child_selectors.size(); ++ci) {
                    generated << " (" << production.child_selectors[ci] << ' '
                              << childSort(production.child_nonterminals[ci]) << ')';
                }
                for (std::size_t vi = 0; vi < production.literal_selectors.size(); ++vi) {
                    generated << " (" << production.literal_selectors[vi] << ' '
                              << production.literal_sorts[vi] << ')';
                }
                generated << ')';
            }
            generated << ')';
        }
        generated << "))\n";

        // Collapse the grammar dependency graph to SCCs, then topologically
        // order those components. Only cyclic SCCs become define-funs-rec
        // groups; acyclic nonterminals remain ordinary define-fun helpers.
        std::vector<std::vector<std::size_t>> edges(live.size());
        for (std::size_t ni = 0; ni < live.size(); ++ni) {
            for (const auto& production : live[ni].productions) {
                for (const auto& child : production.child_nonterminals) {
                    edges[ni].push_back(live_index.at(child));
                }
            }
        }
        std::vector<int> index(live.size(), -1), low(live.size(), -1);
        std::vector<std::size_t> stack;
        std::vector<bool> on_stack(live.size(), false);
        std::vector<std::vector<std::size_t>> components;
        int next = 0;
        std::function<void(std::size_t)> visit = [&](std::size_t node) {
            index[node] = low[node] = next++;
            stack.push_back(node); on_stack[node] = true;
            for (std::size_t child : edges[node]) {
                if (index[child] < 0) { visit(child); low[node] = std::min(low[node], low[child]); }
                else if (on_stack[child]) { low[node] = std::min(low[node], index[child]); }
            }
            if (low[node] != index[node]) return;
            std::vector<std::size_t> component;
            for (;;) {
                const std::size_t member = stack.back(); stack.pop_back(); on_stack[member] = false;
                component.push_back(member); if (member == node) break;
            }
            components.push_back(std::move(component));
        };
        for (std::size_t i = 0; i < live.size(); ++i) if (index[i] < 0) visit(i);
        std::vector<std::size_t> component_of(live.size());
        for (std::size_t ci = 0; ci < components.size(); ++ci)
            for (std::size_t ni : components[ci]) component_of[ni] = ci;
        std::vector<unsigned char> state(components.size(), 0);
        std::vector<std::size_t> component_order;
        std::function<void(std::size_t)> order_component = [&](std::size_t ci) {
            if (state[ci] == 2) return;
            if (state[ci] == 1) return; // condensation is acyclic by construction
            state[ci] = 1;
            for (std::size_t ni : components[ci]) for (std::size_t child : edges[ni])
                if (component_of[child] != ci) order_component(component_of[child]);
            state[ci] = 2; component_order.push_back(ci);
        };
        for (std::size_t i = 0; i < live.size(); ++i) order_component(component_of[i]);

        const auto emitFamily = [&](bool render_family) -> bool {
            for (std::size_t ci : component_order) {
                auto members = components[ci];
                std::sort(members.begin(), members.end());
                const bool self_recursive = members.size() == 1
                    && std::find(edges[members.front()].begin(), edges[members.front()].end(),
                                 members.front()) != edges[members.front()].end();
                const bool recursive = members.size() > 1 || self_recursive;
                const auto functionName = [&](std::size_t ni) -> const std::string& {
                    return render_family ? live[ni].render_name : live[ni].eval_name;
                };
                const auto signature = [&](std::size_t ni) {
                    std::ostringstream sig;
                    sig << '(' << functionName(ni) << " ((" << ast_parameter << ' '
                        << live[ni].ast_sort << ')';
                    if (!render_family) for (std::size_t pi = 0; pi < parameters_.size(); ++pi)
                        sig << " (" << unbounded_eval_parameter_names_[pi] << ' '
                            << parameters_[pi].sort << ')';
                    if (!render_family) for (const Typed& global : target_universal_variables_)
                        sig << " (" << renderSymbol(global.name) << ' '
                            << printSexp(canonicalSort(global.hir_sort)) << ')';
                    sig << ") " << (render_family ? "String" : live[ni].sort) << ')';
                    return sig.str();
                };
                if (recursive) {
                    generated << "(define-funs-rec (";
                    for (std::size_t j = 0; j < members.size(); ++j) {
                        if (j) generated << ' ';
                        generated << signature(members[j]);
                    }
                    generated << ") (";
                } else {
                    generated << "(define-fun " << functionName(members.front())
                              << " ((" << ast_parameter << ' '
                              << live[members.front()].ast_sort << ')';
                    if (!render_family) for (std::size_t pi = 0; pi < parameters_.size(); ++pi)
                        generated << " (" << unbounded_eval_parameter_names_[pi] << ' '
                                  << parameters_[pi].sort << ')';
                    if (!render_family) for (const Typed& global : target_universal_variables_)
                        generated << " (" << renderSymbol(global.name) << ' '
                                  << printSexp(canonicalSort(global.hir_sort)) << ')';
                    generated << ") " << (render_family ? "String" : live[members.front()].sort)
                              << ' ';
                }
                for (std::size_t mi = 0; mi < members.size(); ++mi) {
                    if (mi) generated << ' ';
                    const std::size_t ni = members[mi];
                    std::vector<std::pair<std::string, std::string>> branches;
                    for (const auto& production : live[ni].productions) {
                        std::string template_text;
                        if (!render_family) {
                            template_text = printSexp(production.source_template);
                            std::set<std::string> helper_shadowed;
                            for (const Typed& p : parameters_) helper_shadowed.insert(p.name);
                            const auto& helper_names = candidate_helper_renames_.empty()
                                ? source_helper_targets_
                                : candidate_helper_renames_.front();
                            std::vector<Sexp> parsed;
                            std::string parse_error;
                            SexpReader parser(template_text);
                            if (!parser.readAll(parsed, parse_error) || parsed.size() != 1) {
                                diagnostics.error(ErrorCode::E_INTERNAL,
                                    "unbounded grammar production could not be reparsed");
                                return false;
                            }
                            // Rename helper symbols here, but defer closure
                            // application until after synth parameters are
                            // alpha-renamed below. Closing both before and
                            // after parameter aliasing appends captured global
                            // arguments twice (e.g. `(bump x global global)`).
                            canonicalizeLegacyStringOperators(parsed.front());
                            parsed.front() = renameSynthReferences(
                                parsed.front(), unbounded_synth_wrappers_, helper_shadowed, helper_names);
                            std::map<std::string, std::string> parameter_aliases;
                            for (std::size_t pi = 0; pi < parameters_.size(); ++pi) {
                                parameter_aliases.emplace(parameters_[pi].name,
                                    unbounded_eval_parameter_names_[pi]);
                            }
                            Sexp aliased_parameters = renameEvaluationParameters(
                                parsed.front(), parameter_aliases, {});
                            std::set<std::string> eval_shadowed(
                                unbounded_eval_parameter_names_.begin(),
                                unbounded_eval_parameter_names_.end());
                            Sexp closed_expression = closeExpression(
                                aliased_parameters, eval_shadowed);
                            canonicalizeLegacyStringOperators(closed_expression);
                            const auto emitEval = [&](const auto& self,
                                                      const Sexp& expression) -> std::string {
                                if (expression.isAtom()) {
                                    const auto marker = std::find(production.child_markers.begin(),
                                                                  production.child_markers.end(),
                                                                  expression.atom);
                                    if (marker != production.child_markers.end()) {
                                        const std::size_t child = static_cast<std::size_t>(
                                            marker - production.child_markers.begin());
                                        const std::size_t child_ni = live_index.at(
                                            production.child_nonterminals[child]);
                                        std::string call = "(" + live[child_ni].eval_name
                                            + " (" + production.child_selectors[child]
                                            + " " + ast_parameter + ")";
                                        for (const std::string& parameter_name :
                                             unbounded_eval_parameter_names_)
                                            call += " " + parameter_name;
                                        for (const Typed& global : target_universal_variables_)
                                            call += " " + renderSymbol(global.name);
                                        return call + ")";
                                    }
                                    const auto value_marker = std::find(
                                        production.literal_markers.begin(),
                                        production.literal_markers.end(), expression.atom);
                                    if (value_marker != production.literal_markers.end()) {
                                        const std::size_t value = static_cast<std::size_t>(
                                            value_marker - production.literal_markers.begin());
                                        return "(" + production.literal_selectors[value]
                                             + " " + ast_parameter + ")";
                                    }
                                    return printSexp(expression);
                                }
                                std::string result = "(";
                                for (std::size_t i = 0; i < expression.list.size(); ++i) {
                                    if (i) result += ' ';
                                    result += self(self, expression.list[i]);
                                }
                                return result + ')';
                            };
                            template_text = emitEval(emitEval, closed_expression);
                        } else {
                            const std::string printed = printSexp(production.source_template);
                            std::size_t at = 0;
                            std::vector<std::string> pieces;
                            while (at < printed.size()) {
                                std::size_t best = std::string::npos;
                                std::size_t child = 0;
                                bool is_literal = false;
                                for (std::size_t i = 0; i < production.child_markers.size(); ++i) {
                                    const std::size_t found = printed.find(production.child_markers[i], at);
                                    if (found < best) { best = found; child = i; is_literal = false; }
                                }
                                for (std::size_t i = 0; i < production.literal_markers.size(); ++i) {
                                    const std::size_t found = printed.find(production.literal_markers[i], at);
                                    if (found < best) { best = found; child = i; is_literal = true; }
                                }
                                if (best == std::string::npos) {
                                    pieces.push_back(quoteSmtString(printed.substr(at)));
                                    break;
                                }
                                if (best > at) pieces.push_back(quoteSmtString(printed.substr(at, best - at)));
                                if (is_literal) {
                                    const std::string value = "(" + production.literal_selectors[child]
                                                            + " " + ast_parameter + ")";
                                    const auto concat2 = [](const std::string& left,
                                                            const std::string& right) {
                                        return "(str.++ " + left + " " + right + ")";
                                    };
                                    std::string numeric;
                                    if (production.literal_sorts[child] == "Bool") {
                                        numeric = "(ite " + value + " "
                                                + quoteSmtString("true") + " "
                                                + quoteSmtString("false") + ")";
                                    } else if (production.literal_sorts[child] == "Int") {
                                        const std::string positive = "(str.from_int " + value + ")";
                                        const std::string negated_digits = "(str.from_int (- "
                                            + value + "))";
                                        const std::string negative = concat2(
                                            concat2(quoteSmtString("(- "), negated_digits),
                                            quoteSmtString(")"));
                                        numeric = "(ite (< " + value + " 0) " + negative
                                                + " " + positive + ")";
                                    } else if (production.literal_sorts[child] != "String") {
                                        const std::string digits = "(str.from_int (bv2nat "
                                            + value + "))";
                                        numeric = concat2(concat2(quoteSmtString("(_ bv"), digits),
                                            quoteSmtString(" "
                                                + std::to_string(production.literal_bit_widths[child])
                                                + ")"));
                                    } else {
                                        // The witness is itself source SMT-LIB
                                        // text. Protect each data backslash so
                                        // sequences such as `\\u{41}` survive
                                        // reparsing as literal source content.
                                        const std::string escaped_backslashes =
                                            "(str.replace_all " + value + " "
                                            + quoteSmtString("\\") + " "
                                            + quoteSmtString("\\u{5c}") + ")";
                                        const std::string escaped = "(str.replace_all "
                                            + escaped_backslashes + " "
                                            + quoteSmtString("\"") + " "
                                            + quoteSmtString("\"\"") + ")";
                                        numeric = concat2(concat2(quoteSmtString("\""), escaped),
                                                          quoteSmtString("\""));
                                    }
                                    pieces.push_back(std::move(numeric));
                                    at = best + production.literal_markers[child].size();
                                } else {
                                    const std::size_t child_ni = live_index.at(
                                        production.child_nonterminals[child]);
                                    pieces.push_back("(" + live[child_ni].render_name + " ("
                                        + production.child_selectors[child] + " "
                                        + ast_parameter + "))");
                                    at = best + production.child_markers[child].size();
                                }
                            }
                            if (printed.empty()) pieces.push_back(quoteSmtString(""));
                            if (pieces.size() == 1) template_text = pieces.front();
                            else template_text = "(str.++ " + join(pieces, " ") + ")";
                        }
                        branches.emplace_back("((_ is " + production.constructor
                            + ") " + ast_parameter + ")", std::move(template_text));
                    }
                    if (branches.empty()) {
                        diagnostics.error(ErrorCode::E_INTERNAL,
                                          "productive AST nonterminal has no constructors");
                        return false;
                    }
                    // Datatype constructor tests are disjoint and exhaustive.
                    // Split their alternatives into a balanced decision tree:
                    // a flat list of thousands of grammar terminals must not
                    // create equally deep SMT terms and exhaust parser stacks.
                    const auto emitBranches = [&](const auto& self, std::size_t begin,
                                                  std::size_t end) -> void {
                        if (end - begin == 1) {
                            generated << branches[begin].second;
                            return;
                        }
                        const std::size_t middle = begin + (end - begin) / 2;
                        generated << "(ite ";
                        if (middle - begin > 1) { generated << "(or "; }
                        for (std::size_t branch = begin; branch < middle; ++branch) {
                            if (branch != begin) { generated << ' '; }
                            generated << branches[branch].first;
                        }
                        if (middle - begin > 1) { generated << ')'; }
                        generated << ' ';
                        self(self, begin, middle);
                        generated << ' ';
                        self(self, middle, end);
                        generated << ')';
                    };
                    emitBranches(emitBranches, 0, branches.size());
                }
                generated << (recursive ? "))\n" : ")\n");
            }
            return true;
        };
        if (!emitFamily(false) || !emitFamily(true)) return false;

        function.ast_root_target = prefix + "ast_root_" + std::to_string(function_index);
        function.witness_text_target = prefix + "witness_text_" + std::to_string(function_index);
        generated << "(declare-const " << function.ast_root_target << ' '
                  << live[root_nt].ast_sort << ")\n"
                  << "(declare-const " << function.witness_text_target << " String)\n"
                  << "(assert (= " << function.witness_text_target << " ("
                  << live[root_nt].render_name << ' ' << function.ast_root_target << ")))\n";
        unbounded_prelude_ = generated.str();
        unbounded_candidate_ = "(" + live[root_nt].eval_name + " "
                             + function.ast_root_target;
        for (const Typed& parameter : parameters_) {
            unbounded_candidate_ += " " + renderSymbol(parameter.name);
        }
        for (const Typed& global : target_universal_variables_) {
            unbounded_candidate_ += " " + renderSymbol(global.name);
        }
        unbounded_candidate_ += ")";
        unbounded_source_term_placeholder_ = prefix + "source_term_placeholder_"
                                           + std::to_string(function_index);
        unbounded_source_term_symbol_ = prefix + "source_witness_"
                                     + std::to_string(function_index);
        function.unbounded_prelude = unbounded_prelude_;
        function.unbounded_source_term_placeholder =
            unbounded_source_term_placeholder_;
        function.unbounded_source_term_symbol = unbounded_source_term_symbol_;
        return true;
    }

    bool enumerateCandidates(const std::string& prefix,
                             Uir::Diagnostics& diagnostics) {
        for (std::size_t fi = 0; fi < synth_functions_.size(); ++fi) {
            SynthFunction& function = synth_functions_[fi];
            function_name_ = function.name;
            parameters_ = function.parameters;
            return_sort_ = function.return_sort;
            return_hir_sort_ = function.return_hir_sort;
            active_function_command_index_ = function.command_index;
            default_grammar_requested_ = function.default_grammar_requested;
            grammar_declarations_ = function.grammar_declarations;
            grammar_rules_ = function.grammar_rules;
            nonterminals_.clear();
            nonterminal_indices_.clear();
            memo_.clear();
            estimate_memo_.clear();
            estimate_work_ = 0;
            estimate_budget_exceeded_ = false;
            hole_marker_widths_.clear();
            if (!buildDefaultGrammar(diagnostics) || !readGrammar(diagnostics)) {
                return false;
            }
            if (estimatedTerms(nonterminals_.front().name, depth_)
                > CANDIDATE_LIMIT) {
                if (!buildGrammarCircuit(fi, prefix, diagnostics)) { return false; }
                if (diagnostics.hasErrors()) { return false; }
                function.compact_grammar = !function.empty_bounded_grammar;
                continue;
            }
            function.candidates = terms(nonterminals_.front().name, depth_, diagnostics);
            if (diagnostics.hasErrors()) { return false; }
            if (function.candidates.empty()) {
                function.empty_bounded_grammar = true;
                continue;
            }
            function.bindings.resize(function.candidates.size());
            for (std::size_t i = 0; i < function.candidates.size(); ++i) {
                std::size_t hole_index = 0;
                std::size_t at = function.candidates[i].find(hole_marker_);
                while (at != std::string::npos) {
                    std::size_t marker_size = hole_marker_.size();
                    unsigned bit_width = 0;
                    std::size_t marker_end = at;
                    while (marker_end < function.candidates[i].size()
                           && !std::isspace(static_cast<unsigned char>(
                                  function.candidates[i][marker_end]))
                           && function.candidates[i][marker_end] != '('
                           && function.candidates[i][marker_end] != ')') {
                        ++marker_end;
                    }
                    const auto width = hole_marker_widths_.find(
                        function.candidates[i].substr(at, marker_end - at));
                    if (width != hole_marker_widths_.end()) {
                        marker_size = width->first.size();
                        bit_width = width->second;
                    }
                    const std::string placeholder = hole_prefix_ + std::to_string(fi)
                                                  + "_" + std::to_string(i) + "_"
                                                  + std::to_string(hole_index);
                    function.candidates[i].replace(at, marker_size, placeholder);
                    S::ChoiceAlternative::Binding binding;
                    binding.placeholder = placeholder;
                    binding.target_name = placeholder;
                    binding.kind = bit_width == 0
                                       ? S::ChoiceAlternative::Binding::Kind::INTEGER
                                       : S::ChoiceAlternative::Binding::Kind::BITVECTOR;
                    binding.bit_width = bit_width;
                    function.bindings[i].push_back(std::move(binding));
                    ++hole_index;
                    at = function.candidates[i].find(hole_marker_, at + placeholder.size());
                }
            }
        }
        return true;
    }

    std::size_t addBounded(std::size_t left, std::size_t right) const {
        const std::size_t cap = CANDIDATE_LIMIT + 1;
        return left >= cap || right >= cap || left > cap - right
                   ? cap : left + right;
    }

    std::size_t multiplyBounded(std::size_t left, std::size_t right) const {
        const std::size_t cap = CANDIDATE_LIMIT + 1;
        return left == 0 || right == 0 ? 0
             : left >= cap || right >= cap || left > cap / right ? cap
                                                                  : left * right;
    }

    std::size_t estimatedTerms(const std::string& name, unsigned depth) {
        const auto memoKey = [](const std::string& nt_name, unsigned at_depth) {
            return nt_name + "#estimate#" + std::to_string(at_depth);
        };
        const std::string requested_key = memoKey(name, depth);
        const auto requested = estimate_memo_.find(requested_key);
        if (requested != estimate_memo_.end()) { return requested->second; }

        // A circuit with one nonterminal reference per level exceeds the
        // existing occurrence-node budget beyond this depth. Force the
        // compact path, whose explicit worklist reports that same resource
        // limit without recursing or spending billions of estimator steps.
        if (depth >= GRAMMAR_CIRCUIT_NODE_LIMIT) { return CANDIDATE_LIMIT + 1; }

        // Every nonterminal reference consumes one level. Compute the finite
        // depth recurrence bottom-up, so a recursive grammar cannot consume
        // one C++ stack frame per grammar_depth. Counts are monotone in depth;
        // once the root reaches the candidate cap, larger depths stay on the
        // circuit path.
        for (unsigned current_depth = 0;; ++current_depth) {
            for (const Nonterminal& nt : nonterminals_) {
                if (++estimate_work_ >= GRAMMAR_CIRCUIT_NODE_LIMIT) {
                    estimate_budget_exceeded_ = true;
                    return CANDIDATE_LIMIT + 1;
                }
                const std::string key = memoKey(nt.name, current_depth);
                if (estimate_memo_.find(key) != estimate_memo_.end()) { continue; }
                std::size_t total = 0;
                for (const Sexp& rule : nt.rules) {
                    total = addBounded(total,
                                       estimatedExpression(rule, current_depth));
                    if (estimate_budget_exceeded_) {
                        return CANDIDATE_LIMIT + 1;
                    }
                }
                estimate_memo_.emplace(key, total);
            }
            const auto root_estimate = estimate_memo_.find(memoKey(name, current_depth));
            if (root_estimate == estimate_memo_.end()) { return 0; }
            if (current_depth == depth
                || root_estimate->second >= CANDIDATE_LIMIT + 1) {
                return root_estimate->second;
            }
        }
    }

    std::size_t estimatedExpression(const Sexp& expression, unsigned depth) {
        if (++estimate_work_ >= GRAMMAR_CIRCUIT_NODE_LIMIT) {
            estimate_budget_exceeded_ = true;
            return CANDIDATE_LIMIT + 1;
        }
        if (expression.isAtom()) {
            if (!expression.isStringLiteral() && nonterminal(expression.atom)) {
                if (depth == 0) { return 0; }
                const std::string key = expression.atom + "#estimate#"
                                      + std::to_string(depth - 1);
                const auto cached = estimate_memo_.find(key);
                return cached == estimate_memo_.end() ? 0 : cached->second;
            }
            return 1;
        }
        if (expression.head() == "Constant" && expression.list.size() == 2) {
            std::string sort_text;
            H::Sort sort_value;
            Uir::Diagnostics ignored;
            if (!sort(expression.list[1], sort_text, sort_value, ignored)) {
                return 1;
            }
            return sort_value.kind == H::SortKind::BOOL ? 2 : 1;
        }
        if (expression.head() == "Variable" && expression.list.size() == 2) {
            std::string sort_text;
            H::Sort sort_value;
            Uir::Diagnostics ignored;
            if (!sort(expression.list[1], sort_text, sort_value, ignored)) {
                return 0;
            }
            return static_cast<std::size_t>(std::count_if(
                parameters_.begin(), parameters_.end(), [&](const Typed& parameter) {
                    return H::sameSort(parameter.hir_sort, sort_value);
                }));
        }
        std::size_t product = 1;
        for (const Sexp& child : expression.list) {
            product = multiplyBounded(product, estimatedExpression(child, depth));
        }
        return product;
    }

    bool buildGrammarCircuit(std::size_t function_index,
                             const std::string& prefix,
                             Uir::Diagnostics& diagnostics) {
        SynthFunction& function = synth_functions_[function_index];
        function.grammar_choice.source_name = "definition[" + function.name + "]";
        function.grammar_choice.prefix = "(define-fun " + renderSymbol(function.name) + " "
            + binder(function.parameters) + " " + function.return_sort + " ";
        function.grammar_choice.suffix = ")";
        function.grammar_choice.root_node = 0;
        std::size_t next_binding = 0;
        const std::size_t invalid = std::numeric_limits<std::size_t>::max();
        bool node_budget_exceeded = false;

        const auto addNode = [&]() -> std::size_t {
            if (function.grammar_choice.nodes.size() >= GRAMMAR_CIRCUIT_NODE_LIMIT) {
                node_budget_exceeded = true;
                diagnostics.error(ErrorCode::E_RESOURCE,
                                  "SyGuS bounded grammar circuit exceeds "
                                      + std::to_string(GRAMMAR_CIRCUIT_NODE_LIMIT)
                                      + " production-occurrence nodes");
                return invalid;
            }
            const std::size_t index = function.grammar_choice.nodes.size();
            S::GrammarChoiceNode node;
            node.selector_target = prefix + "grammar_select_"
                                 + std::to_string(function_index) + "_"
                                 + std::to_string(index);
            function.compact_selectors.push_back(node.selector_target);
            function.grammar_choice.nodes.push_back(std::move(node));
            return index;
        };

        std::function<std::size_t(const Sexp&, unsigned)> makeExpressionNode;
        std::function<std::size_t(const std::string&, unsigned)> makeNonterminalNode;
        std::function<bool(const Sexp&, unsigned,
                           std::vector<S::GrammarChoiceAlternative>&)> makeAlternatives;
        struct NonterminalWork {
            std::size_t node;
            std::string name;
            unsigned remaining;
        };
        std::vector<NonterminalWork> pending_nonterminals;
        std::set<std::string> parameter_names;
        for (const Typed& parameter : parameters_) {
            parameter_names.insert(parameter.name);
        }

        makeAlternatives = [&](const Sexp& expression, unsigned remaining,
                               std::vector<S::GrammarChoiceAlternative>& result) -> bool {
            if (expression.isAtom()) {
                if (!expression.isStringLiteral() && nonterminal(expression.atom)) {
                    if (remaining == 0) { return true; }
                    const std::size_t child = makeNonterminalNode(expression.atom,
                                                                  remaining - 1);
                    if (child == invalid) { return true; }
                    S::GrammarChoiceAlternative alternative;
                    const std::string placeholder = prefix + "grammar_child_"
                        + std::to_string(function_index) + "_"
                        + std::to_string(function.grammar_choice.nodes.size()) + "_"
                        + std::to_string(result.size());
                    alternative.label = placeholder;
                    alternative.child_placeholders.push_back(placeholder);
                    alternative.children.push_back(child);
                    result.push_back(std::move(alternative));
                    return true;
                }
                S::GrammarChoiceAlternative alternative;
                alternative.label = expression.isStringLiteral()
                    ? printSexp(expression)
                    : (!expression.quoted_symbol
                       && legacyNegativeInteger(expression.atom)
                    && !declaredGrammarSymbol(expression.atom)
                    ? "(- " + expression.atom.substr(1) + ")"
                    : printSexp(expression));
                result.push_back(std::move(alternative));
                return true;
            }
            if (expression.head() == "Constant") {
                if (expression.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed (Constant Sort) grammar term");
                    return false;
                }
                std::string constant_sort;
                H::Sort constant_hir;
                if (!sort(expression.list[1], constant_sort, constant_hir, diagnostics)) {
                    return false;
                }
                if (constant_hir.kind == H::SortKind::BOOL) {
                    result.push_back({"false", {}, {}, {}});
                    result.push_back({"true", {}, {}, {}});
                    return true;
                }
                if (constant_hir.kind != H::SortKind::INT
                    && constant_hir.kind != H::SortKind::BITVEC) {
                    diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                      "unsupported SyGuS Constant sort " + constant_sort);
                    return false;
                }
                S::GrammarChoiceAlternative alternative;
                const std::string placeholder = prefix + "grammar_constant_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(next_binding++);
                alternative.label = placeholder;
                S::ChoiceAlternative::Binding binding;
                binding.placeholder = placeholder;
                binding.target_name = placeholder;
                binding.kind = constant_hir.kind == H::SortKind::BITVEC
                    ? S::ChoiceAlternative::Binding::Kind::BITVECTOR
                    : S::ChoiceAlternative::Binding::Kind::INTEGER;
                binding.bit_width = constant_hir.width;
                alternative.bindings.push_back(binding);
                function.compact_bindings.push_back(std::move(binding));
                result.push_back(std::move(alternative));
                return true;
            }
            if (expression.head() == "Variable") {
                if (expression.list.size() != 2) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed (Variable Sort) grammar term");
                    return false;
                }
                std::string wanted;
                H::Sort wanted_hir;
                if (!sort(expression.list[1], wanted, wanted_hir, diagnostics)) {
                    return false;
                }
                for (const Typed& parameter : parameters_) {
                    if (H::sameSort(parameter.hir_sort, wanted_hir)) {
                        result.push_back({renderSymbol(parameter.name), {}, {}, {}});
                    }
                }
                return true;
            }
            if (expression.head() == "let" || expression.head() == "!") {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "grammar let/weighted annotations need scope and weight tracking");
                return false;
            }
            if (expression.list.empty()) {
                result.push_back({"()", {}, {}, {}});
                return true;
            }
            if (!expression.list.front().isAtom()) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "grammar application has a non-symbol operator");
                return false;
            }
            S::GrammarChoiceAlternative alternative;
            alternative.label = "(" + printSexp(expression.list.front());
            for (std::size_t i = 1; i < expression.list.size(); ++i) {
                const std::size_t child = makeExpressionNode(expression.list[i], remaining);
                if (child == invalid) { return true; }
                const std::string placeholder = prefix + "grammar_child_"
                    + std::to_string(function_index) + "_"
                    + std::to_string(function.grammar_choice.nodes.size()) + "_"
                    + std::to_string(i - 1);
                alternative.label += " " + placeholder;
                alternative.child_placeholders.push_back(placeholder);
                alternative.children.push_back(child);
            }
            alternative.label += ")";
            result.push_back(std::move(alternative));
            return true;
        };

        makeExpressionNode = [&](const Sexp& expression, unsigned remaining) -> std::size_t {
            if (expression.isAtom() && !expression.isStringLiteral()
                && nonterminal(expression.atom)) {
                if (remaining == 0) { return invalid; }
                return makeNonterminalNode(expression.atom, remaining - 1);
            }
            const std::size_t index = addNode();
            if (index == invalid) { return invalid; }
            std::vector<S::GrammarChoiceAlternative> alternatives;
            if (!makeAlternatives(expression, remaining, alternatives)) { return invalid; }
            function.grammar_choice.nodes[index].alternatives = std::move(alternatives);
            if (function.grammar_choice.nodes[index].alternatives.size() == 1) {
                function.grammar_choice.nodes[index].selector_target.clear();
            }
            return index;
        };

        makeNonterminalNode = [&](const std::string& name, unsigned remaining) -> std::size_t {
            const Nonterminal* nt = nonterminal(name);
            if (!nt) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar references undeclared nonterminal '" + name + "'");
                return invalid;
            }
            const std::size_t index = addNode();
            if (index == invalid) { return invalid; }
            pending_nonterminals.push_back({index, name, remaining});
            return index;
        };

        const std::size_t root = makeNonterminalNode(nonterminals_.front().name, depth_);
        if (root == invalid) { return false; }
        // Nonterminal recursion decreases `remaining`, so expand it as an
        // explicit queue rather than consuming one C++ stack frame per depth.
        // Expression nesting is still traversed structurally by the Sexp
        // helpers, while the benchmark's recursive grammar chains are bounded
        // by the existing node budget rather than the process stack size.
        for (std::size_t cursor = 0; cursor < pending_nonterminals.size(); ++cursor) {
            const NonterminalWork work = pending_nonterminals[cursor];
            const Nonterminal* nt = nonterminal(work.name);
            if (!nt) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "queued grammar nonterminal disappeared");
                return false;
            }
            std::vector<S::GrammarChoiceAlternative> alternatives;
            for (const Sexp& rule : nt->rules) {
                std::vector<S::GrammarChoiceAlternative> production_alternatives;
                if (!makeAlternatives(rule, work.remaining, production_alternatives)) {
                    return false;
                }
                if (node_budget_exceeded) { return false; }
                // Keep `alternative.label` in source syntax: the projection
                // contract uses it to reconstruct a source witness. Target
                // closure arguments and reserved-name aliases are applied by
                // renderAlternative below, when building only the SMT body.
                alternatives.insert(alternatives.end(),
                                    std::make_move_iterator(production_alternatives.begin()),
                                    std::make_move_iterator(production_alternatives.end()));
            }
            function.grammar_choice.nodes[work.node].alternatives =
                std::move(alternatives);
            if (function.grammar_choice.nodes[work.node].alternatives.size() == 1) {
                function.grammar_choice.nodes[work.node].selector_target.clear();
            }
        }
        // Remove productions whose deferred nonterminal children have no
        // bounded derivation. Node indices are allocated parent-before-child,
        // so one reverse pass computes productivity for this acyclic
        // depth-unrolled circuit.
        std::vector<bool> productive(function.grammar_choice.nodes.size(), false);
        for (std::size_t index = function.grammar_choice.nodes.size(); index-- > 0;) {
            auto& alternatives = function.grammar_choice.nodes[index].alternatives;
            alternatives.erase(std::remove_if(alternatives.begin(), alternatives.end(),
                [&](const S::GrammarChoiceAlternative& alternative) {
                    return std::any_of(alternative.children.begin(), alternative.children.end(),
                        [&](std::size_t child) { return !productive[child]; });
                }), alternatives.end());
            productive[index] = !alternatives.empty();
            if (alternatives.size() == 1) {
                function.grammar_choice.nodes[index].selector_target.clear();
            }
        }
        if (function.grammar_choice.nodes[root].alternatives.empty()) {
            function.empty_bounded_grammar = true;
            function.grammar_choice.nodes.clear();
            return true;
        }
        function.grammar_choice.root_node = root;

        // Remove nodes reachable only from unproductive productions. Their
        // selectors/constants must not constrain the actual grammar circuit.
        std::vector<bool> reachable(function.grammar_choice.nodes.size(), false);
        std::vector<std::size_t> pending_nodes{root};
        while (!pending_nodes.empty()) {
            const std::size_t index = pending_nodes.back();
            pending_nodes.pop_back();
            if (reachable[index]) { continue; }
            reachable[index] = true;
            for (const auto& alternative :
                 function.grammar_choice.nodes[index].alternatives) {
                pending_nodes.insert(pending_nodes.end(),
                                     alternative.children.begin(),
                                     alternative.children.end());
            }
        }
        std::vector<std::size_t> remap(reachable.size(), invalid);
        std::vector<S::GrammarChoiceNode> compact_nodes;
        for (std::size_t i = 0; i < reachable.size(); ++i) {
            if (reachable[i]) {
                remap[i] = compact_nodes.size();
                compact_nodes.push_back(std::move(function.grammar_choice.nodes[i]));
            }
        }
        for (auto& node : compact_nodes) {
            for (auto& alternative : node.alternatives) {
                for (std::size_t& child : alternative.children) { child = remap[child]; }
            }
        }
        function.grammar_choice.root_node = remap[root];
        function.grammar_choice.nodes = std::move(compact_nodes);
        function.compact_selectors.clear();
        function.compact_bindings.clear();
        for (const auto& node : function.grammar_choice.nodes) {
            if (!node.selector_target.empty()) {
                function.compact_selectors.push_back(node.selector_target);
            }
            for (const auto& alternative : node.alternatives) {
                function.compact_bindings.insert(function.compact_bindings.end(),
                    alternative.bindings.begin(), alternative.bindings.end());
            }
        }

        // Keep the emitted formula linear in the circuit size. Expanding every
        // child into every parent duplicates a depth-n unary grammar O(n^2)
        // bytes (and caches all those copies); topologically nested lets share
        // each node's selected value. Selector variables remain outside the
        // source-input forall wrapper, so choices are fixed per candidate.
        const auto& nodes = function.grammar_choice.nodes;
        std::vector<std::size_t> depths(nodes.size(), invalid);
        std::vector<std::vector<std::size_t>> levels;
        std::vector<std::size_t> queue{function.grammar_choice.root_node};
        depths[function.grammar_choice.root_node] = 0;
        for (std::size_t cursor = 0; cursor < queue.size(); ++cursor) {
            const std::size_t parent = queue[cursor];
            const std::size_t child_depth = depths[parent] + 1;
            for (const auto& alternative : nodes[parent].alternatives) {
                for (std::size_t child : alternative.children) {
                    if (depths[child] == invalid) {
                        depths[child] = child_depth;
                        queue.push_back(child);
                    } else if (depths[child] != child_depth) {
                        diagnostics.error(ErrorCode::E_INTERNAL,
                                          "grammar circuit node is shared across depths");
                        return false;
                    }
                }
            }
        }
        for (std::size_t index = 0; index < depths.size(); ++index) {
            if (depths[index] == invalid) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "grammar circuit contains an unreachable node");
                return false;
            }
            if (levels.size() <= depths[index]) { levels.resize(depths[index] + 1); }
            levels[depths[index]].push_back(index);
        }

        std::vector<std::string> value_names(nodes.size());
        for (std::size_t i = 0; i < nodes.size(); ++i) {
            value_names[i] = prefix + "grammar_value_"
                           + std::to_string(function_index) + "_" + std::to_string(i);
        }
        const auto renderAlternative = [&](const S::GrammarChoiceAlternative& alternative,
                                           std::string& rendered) -> bool {
            std::vector<Sexp> parsed;
            std::string error;
            std::string target_template;
            if (!renameHelperCalls(alternative.label, source_helper_targets_,
                                   parameter_names, target_template, diagnostics)) {
                return false;
            }
            SexpReader reader(target_template);
            if (!reader.readAll(parsed, error) || parsed.size() != 1) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "malformed grammar production template: " + error);
                return false;
            }
            std::map<std::string, std::string> replacement;
            for (std::size_t i = 0; i < alternative.children.size(); ++i) {
                replacement.emplace(alternative.child_placeholders[i],
                                    value_names[alternative.children[i]]);
            }
            std::map<std::string, std::size_t> occurrences;
            const auto substitute = [&](const auto& self, Sexp& expression) -> void {
                if (expression.isAtom()) {
                    if (expression.isStringLiteral()) { return; }
                    const auto found = replacement.find(expression.atom);
                    if (found != replacement.end()) {
                        expression = symbolSexp(found->second);
                        ++occurrences[found->first];
                    }
                    return;
                }
                for (Sexp& child : expression.list) { self(self, child); }
            };
            substitute(substitute, parsed.front());
            for (const auto& child : replacement) {
                if (occurrences[child.first] == 0) {
                    diagnostics.error(ErrorCode::E_INTERNAL,
                                      "grammar template is missing child placeholder '"
                                          + child.first + "'");
                    return false;
                }
            }
            rendered = printSexp(parsed.front());
            return true;
        };
        std::vector<std::string> right_hand_sides(nodes.size());
        for (std::size_t index = 0; index < nodes.size(); ++index) {
            const auto& node = nodes[index];
            std::vector<std::string> terms;
            for (const auto& alternative : node.alternatives) {
                std::string term;
                if (!renderAlternative(alternative, term)) { return false; }
                terms.push_back(std::move(term));
            }
            if (terms.empty()) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "grammar circuit contains an unproductive node");
                return false;
            }
            std::string result = terms.back();
            for (std::size_t i = terms.size() - 1; i-- > 0;) {
                result = "(ite (= " + renderSymbol(node.selector_target) + " "
                       + std::to_string(i) + ") " + terms[i] + " " + result + ")";
            }
            right_hand_sides[index] = std::move(result);
        }
        function.compact_smt_body.clear();
        for (auto level = levels.rbegin(); level != levels.rend(); ++level) {
            function.compact_smt_body += "(let (";
            for (std::size_t i = 0; i < level->size(); ++i) {
                if (i != 0) { function.compact_smt_body += " "; }
                const std::size_t index = (*level)[i];
                function.compact_smt_body += "(" + renderSymbol(value_names[index]) + " "
                                           + right_hand_sides[index] + ")";
            }
            function.compact_smt_body += ") ";
        }
        function.compact_smt_body += renderSymbol(value_names[
            function.grammar_choice.root_node]);
        function.compact_smt_body.append(levels.size(), ')');
        return true;
    }

    bool buildDefaultGrammar(Uir::Diagnostics& diagnostics) {
        if (!default_grammar_requested_) { return true; }
        if (logic_name_ == "BV") {
            // Reference grammar B.3 from SyGuS-IF 2.1, generalized to each
            // bit-width present in this function's signature. The standard
            // permits any output-logic term when a grammar is omitted; this
            // finite enumerator supports the documented B.3 operator
            // fragment, core equality/distinct, and the common SMT-LIB
            // fixed-width extensions listed below. It does not claim to
            // enumerate every output-logic term (for example, concat/extract).
            default_nt_prefix_ = "__somt_sygus_default_nt_";
            while (source_.find(default_nt_prefix_) != std::string::npos) {
                default_nt_prefix_ += "x";
            }
            std::set<unsigned> widths;
            for (const Typed& parameter : parameters_) {
                unsigned width = 0;
                if (bitVectorWidth(parameter.sort, width)) { widths.insert(width); }
            }
            unsigned result_width = 0;
            if (bitVectorWidth(return_sort_, result_width)) { widths.insert(result_width); }
            if (widths.empty() && return_sort_ != "Bool") {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "the BV default grammar supports Bool or BitVec results");
                return false;
            }
            const Sexp bool_sort = atom("Bool");
            const Sexp bool_nt = atom(default_nt_prefix_ + "B");
            std::vector<Sexp> declarations;
            std::vector<Sexp> groups;
            std::map<unsigned, Sexp> bitvec_nts;
            for (unsigned width : widths) {
                Sexp nt = atom(default_nt_prefix_ + "BV" + std::to_string(width));
                bitvec_nts.emplace(width, nt);
            }
            if (return_sort_ == "Bool") {
                declarations.push_back(form({bool_nt, bool_sort}));
            } else {
                declarations.push_back(form({bitvec_nts.at(result_width),
                                             indexedSort(result_width)}));
            }
            for (const auto& [width, nt] : bitvec_nts) {
                if (return_sort_ == "Bool" || width != result_width) {
                    declarations.push_back(form({nt, indexedSort(width)}));
                }
            }
            if (return_sort_ != "Bool") {
                declarations.push_back(form({bool_nt, bool_sort}));
            }
            for (const auto& [width, nt] : bitvec_nts) {
                const Sexp sort = indexedSort(width);
                std::vector<Sexp> rules{
                    application("Constant", {sort}),
                    application("Variable", {sort}),
                    application("bvnot", {nt}),
                    application("bvand", {nt, nt}),
                    application("bvor", {nt, nt}),
                    application("bvxor", {nt, nt}),
                    application("bvnand", {nt, nt}),
                    application("bvnor", {nt, nt}),
                    application("bvxnor", {nt, nt}),
                    application("bvneg", {nt}),
                    application("bvadd", {nt, nt}),
                    application("bvsub", {nt, nt}),
                    application("bvmul", {nt, nt}),
                    application("bvudiv", {nt, nt}),
                    application("bvurem", {nt, nt}),
                    application("bvsdiv", {nt, nt}),
                    application("bvsrem", {nt, nt}),
                    application("bvsmod", {nt, nt}),
                    application("bvshl", {nt, nt}),
                    application("bvlshr", {nt, nt}),
                    application("bvashr", {nt, nt}),
                    application("ite", {bool_nt, nt, nt})};
                groups.push_back(form({nt, sort, form(rules)}));
            }
            std::vector<Sexp> boolean_rules{
                application("Constant", {bool_sort}),
                application("Variable", {bool_sort})};
            for (const auto& [width, nt] : bitvec_nts) {
                (void)width;
                boolean_rules.push_back(application("=", {nt, nt}));
                boolean_rules.push_back(application("distinct", {nt, nt}));
                boolean_rules.push_back(application("bvult", {nt, nt}));
                boolean_rules.push_back(application("bvule", {nt, nt}));
                boolean_rules.push_back(application("bvugt", {nt, nt}));
                boolean_rules.push_back(application("bvuge", {nt, nt}));
                boolean_rules.push_back(application("bvslt", {nt, nt}));
                boolean_rules.push_back(application("bvsle", {nt, nt}));
                boolean_rules.push_back(application("bvsgt", {nt, nt}));
                boolean_rules.push_back(application("bvsge", {nt, nt}));
            }
            boolean_rules.push_back(application("=", {bool_nt, bool_nt}));
            boolean_rules.push_back(application("distinct", {bool_nt, bool_nt}));
            boolean_rules.push_back(application("not", {bool_nt}));
            boolean_rules.push_back(application("and", {bool_nt, bool_nt}));
            boolean_rules.push_back(application("or", {bool_nt, bool_nt}));
            boolean_rules.push_back(application("=>", {bool_nt, bool_nt}));
            boolean_rules.push_back(application("xor", {bool_nt, bool_nt}));
            boolean_rules.push_back(application("ite", {bool_nt, bool_nt, bool_nt}));
            groups.push_back(form({bool_nt, bool_sort, form(boolean_rules)}));
            grammar_declarations_ = form(declarations);
            grammar_rules_ = form(groups);
            return true;
        }
        if (logic_name_ == "SAT") {
            if (return_sort_ != "Bool") {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "the SAT default grammar is available for Bool invariants only");
                return false;
            }
            default_nt_prefix_ = "__somt_sygus_default_nt_";
            while (source_.find(default_nt_prefix_) != std::string::npos) {
                default_nt_prefix_ += "x";
            }
            const Sexp boolean_sort = atom("Bool");
            const Sexp boolean_nt = atom(default_nt_prefix_ + "B");
            std::vector<Sexp> boolean_rules{
                atom("true"), atom("false"),
                application("Variable", {boolean_sort}),
                application("not", {boolean_nt}),
                application("and", {boolean_nt, boolean_nt}),
                application("or", {boolean_nt, boolean_nt}),
                application("=>", {boolean_nt, boolean_nt}),
                application("xor", {boolean_nt, boolean_nt}),
                application("=", {boolean_nt, boolean_nt}),
                application("distinct", {boolean_nt, boolean_nt}),
                application("ite", {boolean_nt, boolean_nt, boolean_nt})};
            grammar_declarations_ = form({form({boolean_nt, boolean_sort})});
            grammar_rules_ = form({
                form({boolean_nt, boolean_sort, form(boolean_rules)})});
            return true;
        }
        if (logic_name_ != "LIA" && logic_name_ != "NIA") {
            diagnostics.error(
                ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                "default grammar is currently supported for SyGuS LIA and NIA only");
            return false;
        }

        const Sexp int_sort = atom("Int");
        const Sexp bool_sort = atom("Bool");
        default_nt_prefix_ = "__somt_sygus_default_nt_";
        while (source_.find(default_nt_prefix_) != std::string::npos) {
            default_nt_prefix_ += "x";
        }
        const Sexp int_nt = atom(default_nt_prefix_ + "I");
        const Sexp constant_nt = atom(default_nt_prefix_ + "C");
        const Sexp bool_nt = atom(default_nt_prefix_ + "B");
        std::vector<Sexp> integer_rules{
            constant_nt,
            application("Variable", {int_sort}),
            application("-", {int_nt}),
            application("+", {int_nt, int_nt}),
            application("-", {int_nt, int_nt}),
            application("ite", {bool_nt, int_nt, int_nt})};
        if (logic_name_ == "LIA") {
            integer_rules.push_back(application("*", {constant_nt, int_nt}));
            integer_rules.push_back(application("*", {int_nt, constant_nt}));
            integer_rules.push_back(application("div", {int_nt, constant_nt}));
            integer_rules.push_back(application("mod", {int_nt, constant_nt}));
        } else {
            integer_rules.push_back(application("*", {int_nt, int_nt}));
            integer_rules.push_back(application("div", {int_nt, int_nt}));
            integer_rules.push_back(application("mod", {int_nt, int_nt}));
        }
        integer_rules.push_back(application("abs", {int_nt}));

        std::vector<Sexp> boolean_rules{
            atom("true"), atom("false"),
            application("Variable", {bool_sort}),
            application("not", {bool_nt}),
            application("and", {bool_nt, bool_nt}),
            application("or", {bool_nt, bool_nt}),
            application("=>", {bool_nt, bool_nt}),
            application("xor", {bool_nt, bool_nt}),
            application("=", {bool_nt, bool_nt}),
            application("distinct", {bool_nt, bool_nt}),
            application("ite", {bool_nt, bool_nt, bool_nt}),
            application("=", {int_nt, int_nt}),
            application("distinct", {int_nt, int_nt}),
            application("<", {int_nt, int_nt}),
            application("<=", {int_nt, int_nt}),
            application(">", {int_nt, int_nt}),
            application(">=", {int_nt, int_nt})};

        const bool returns_integer = return_sort_ == "Int";
        const Sexp start_nt = returns_integer ? int_nt : bool_nt;
        const Sexp start_sort = returns_integer ? int_sort : bool_sort;
        grammar_declarations_ = form({
            form({start_nt, start_sort}),
            form({returns_integer ? constant_nt : int_nt, int_sort}),
            form({returns_integer ? bool_nt : constant_nt,
                  returns_integer ? bool_sort : int_sort})});
        if (returns_integer) {
            grammar_rules_ = form({
                form({int_nt, int_sort, form(integer_rules)}),
                form({constant_nt, int_sort,
                      form({application("Constant", {int_sort})})}),
                form({bool_nt, bool_sort, form(boolean_rules)})});
        } else {
            grammar_rules_ = form({
                form({bool_nt, bool_sort, form(boolean_rules)}),
                form({int_nt, int_sort, form(integer_rules)}),
                form({constant_nt, int_sort,
                      form({application("Constant", {int_sort})})})});
        }
        return true;
    }

    bool readGrammar(Uir::Diagnostics& diagnostics) {
        if (grammar_declarations_.isAtom() || grammar_declarations_.list.empty()
            || grammar_rules_.isAtom()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "malformed SyGuS grammar declaration/rule lists");
            return false;
        }
        std::map<std::string, std::size_t> indices;
        for (const Sexp& declaration : grammar_declarations_.list) {
            if (declaration.list.size() != 2 || !declaration.list[0].isAtom()
                || !simpleSymbol(declaration.list[0])) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed grammar nonterminal declaration");
                return false;
            }
            Nonterminal nonterminal;
            nonterminal.name = declaration.list[0].atom;
            if (!sort(declaration.list[1], nonterminal.sort,
                      nonterminal.hir_sort, diagnostics)) {
                return false;
            }
            if (!indices.emplace(nonterminal.name, nonterminals_.size()).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "duplicate grammar nonterminal '" + nonterminal.name + "'");
                return false;
            }
            nonterminals_.push_back(std::move(nonterminal));
        }
        nonterminal_indices_ = indices;
        if (!H::sameSort(nonterminals_.front().hir_sort, return_hir_sort_)) {
            diagnostics.error(ErrorCode::E_TYPE,
                              "the first grammar nonterminal must have synth-fun return sort");
            return false;
        }
        std::set<std::string> defined;
        for (const Sexp& grouped : grammar_rules_.list) {
            if (grouped.list.size() != 3 || !grouped.list[0].isAtom()
                || grouped.list[2].isAtom()) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed grouped grammar rule listing");
                return false;
            }
            const auto found = indices.find(grouped.list[0].atom);
            if (found == indices.end() || !defined.insert(grouped.list[0].atom).second) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "grammar rule names an undeclared or duplicate nonterminal '"
                                      + grouped.list[0].atom + "'");
                return false;
            }
            std::string rule_sort;
            H::Sort rule_hir;
            if (!sort(grouped.list[1], rule_sort, rule_hir, diagnostics)) { return false; }
            if (!H::sameSort(rule_hir, nonterminals_[found->second].hir_sort)) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar rule sort disagrees with nonterminal declaration");
                return false;
            }
            nonterminals_[found->second].rules = grouped.list[2].list;
        }
        if (defined.size() != nonterminals_.size()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "every grammar nonterminal requires one grouped rule listing");
            return false;
        }
        for (const Nonterminal& nt : nonterminals_) {
            for (const Sexp& rule : nt.rules) {
                H::Sort actual;
                if (!productionSort(rule, actual, diagnostics)) { return false; }
                if (!H::sameSort(actual, nt.hir_sort)) {
                    diagnostics.error(
                        ErrorCode::E_TYPE,
                        "grammar production '" + printSexp(rule) + "' for nonterminal '"
                            + nt.name + "' has the wrong sort; expected " + nt.sort);
                    return false;
                }
            }
        }
        return true;
    }

    bool declaredGrammarSymbol(const std::string& name) const {
        for (const Typed& parameter : parameters_) {
            if (parameter.name == name) { return true; }
        }
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            if (definitions_[i].list[1].atom == name
                && definition_command_indices_[i] < active_function_command_index_) {
                return true;
            }
        }
        return false;
    }

    bool productionSort(const Sexp& expression, H::Sort& result,
                        Uir::Diagnostics& diagnostics) const {
        if (expression.isAtom()) {
            if (expression.isStringLiteral()) {
                result = H::Sort::string();
                return true;
            }
            if (const Nonterminal* nt = nonterminal(expression.atom)) {
                result = nt->hir_sort;
                return true;
            }
            if (!expression.quoted_symbol
                && (expression.atom == "true" || expression.atom == "false")) {
                result = H::Sort::boolean();
                return true;
            }
            if (!expression.quoted_symbol
                && std::all_of(expression.atom.begin(), expression.atom.end(),
                               [](unsigned char c) { return std::isdigit(c) != 0; })) {
                result = H::Sort::integer();
                return true;
            }
            if (!expression.quoted_symbol && expression.atom.size() > 2
                && (expression.atom.compare(0, 2, "#b") == 0
                    || expression.atom.compare(0, 2, "#x") == 0)) {
                const bool binary = expression.atom[1] == 'b';
                const std::size_t digits = expression.atom.size() - 2;
                const auto valid_digit = [binary](unsigned char c) {
                    if (binary) { return c == '0' || c == '1'; }
                    return std::isxdigit(c) != 0;
                };
                if (digits == 0
                    || !std::all_of(expression.atom.begin() + 2, expression.atom.end(),
                                    valid_digit)
                    || digits > std::numeric_limits<unsigned>::max() / (binary ? 1U : 4U)) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "malformed SyGuS bit-vector literal '"
                                          + expression.atom + "'");
                    return false;
                }
                result = H::Sort::bitvec(static_cast<unsigned>(digits * (binary ? 1U : 4U)));
                return true;
            }
            const auto formal = std::find_if(
                parameters_.begin(), parameters_.end(), [&](const Typed& parameter) {
                    return parameter.name == expression.atom;
                });
            if (formal != parameters_.end()) {
                result = formal->hir_sort;
                return true;
            }
            for (std::size_t i = 0; i < definitions_.size(); ++i) {
                if (definitions_[i].list[1].atom == expression.atom
                    && definition_command_indices_[i] < active_function_command_index_
                    && definition_parameters_[i].empty()) {
                    std::string ignored;
                    return sort(definitions_[i].list[3], ignored, result, diagnostics);
                }
            }
            if (!expression.quoted_symbol && legacyNegativeInteger(expression.atom)
                && !declaredGrammarSymbol(expression.atom)) {
                result = H::Sort::integer();
                return true;
            }
            diagnostics.error(ErrorCode::E_TYPE,
                              "grammar uses undeclared terminal/nonterminal '"
                                  + expression.atom + "'");
            return false;
        }
        if (expression.list.size() == 3 && expression.list[0].isAtom()
            && expression.list[0].atom == "_" && expression.list[1].isAtom()
            && expression.list[1].atom.compare(0, 2, "bv") == 0
            && expression.list[2].isAtom()) {
            const std::string numeral = expression.list[1].atom.substr(2);
            const std::string& width_text = expression.list[2].atom;
            unsigned long width = 0;
            try {
                if (!unsignedDecimal(width_text)) {
                    throw std::invalid_argument("non-decimal BitVec width");
                }
                std::size_t consumed = 0;
                width = std::stoul(width_text, &consumed);
                if (consumed != width_text.size() || width == 0
                    || width > std::numeric_limits<unsigned>::max()) {
                    throw std::out_of_range("BitVec width");
                }
            } catch (const std::exception&) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "indexed SyGuS bit-vector literal requires a positive width");
                return false;
            }
            if (!unsignedDecimal(numeral)) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "indexed SyGuS bit-vector literal requires a decimal numeral");
                return false;
            }
            result = H::Sort::bitvec(static_cast<unsigned>(width));
            return true;
        }
        if (expression.head() == "Variable" || expression.head() == "Constant") {
            if (expression.list.size() != 2) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed (" + expression.head()
                                      + " Sort) grammar production");
                return false;
            }
            std::string ignored;
            return sort(expression.list[1], ignored, result, diagnostics);
        }
        if (expression.head() == "let" || expression.head() == "!") {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "grammar let/weighted annotations need scope and weight tracking");
            return false;
        }
        if (expression.list.empty()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "grammar production has no supported operator head");
            return false;
        }
        std::string op;
        std::vector<unsigned> indices;
        if (expression.list.front().isAtom()) {
            op = expression.list.front().atom;
        } else {
            const Sexp& indexed = expression.list.front();
            if (indexed.list.size() < 2 || indexed.list[0].atom != "_"
                || !indexed.list[1].isAtom()) {
                diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                                  "unsupported indexed SyGuS grammar operator");
                return false;
            }
            op = indexed.list[1].atom;
            for (std::size_t i = 2; i < indexed.list.size(); ++i) {
                if (!indexed.list[i].isAtom()) {
                    diagnostics.error(ErrorCode::E_PARSE,
                                      "malformed indexed SyGuS grammar operator");
                    return false;
                }
                try {
                    if (!unsignedDecimal(indexed.list[i].atom)) {
                        throw std::invalid_argument("non-decimal operator index");
                    }
                    std::size_t consumed = 0;
                    const unsigned long value = std::stoul(indexed.list[i].atom, &consumed);
                    if (consumed != indexed.list[i].atom.size()
                        || value > std::numeric_limits<unsigned>::max()) {
                        throw std::out_of_range("operator index");
                    }
                    indices.push_back(static_cast<unsigned>(value));
                } catch (const std::exception&) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "indexed SyGuS operators require nonnegative integer indices");
                    return false;
                }
            }
        }
        if (op == "int.to.str" && isBuiltinInSourceLogic(op)) {
            op = "str.from_int";
        } else if (op == "str.to.int" && isBuiltinInSourceLogic(op)) {
            op = "str.to_int";
        }
        std::vector<H::Sort> arguments;
        for (std::size_t i = 1; i < expression.list.size(); ++i) {
            H::Sort argument;
            if (!productionSort(expression.list[i], argument, diagnostics)) {
                return false;
            }
            arguments.push_back(std::move(argument));
        }

        const auto arity = [&](std::size_t minimum, std::size_t maximum) {
            if (arguments.size() >= minimum && arguments.size() <= maximum) {
                return true;
            }
            diagnostics.error(ErrorCode::E_TYPE,
                              "grammar operator '" + op + "' has invalid arity "
                                  + std::to_string(arguments.size()));
            return false;
        };
        const auto allSort = [&](const H::Sort& expected) {
            return std::all_of(arguments.begin(), arguments.end(),
                               [&](const H::Sort& argument) {
                                   return H::sameSort(argument, expected);
                               });
        };
        const auto expectArguments = [&](const H::Sort& expected) {
            if (allSort(expected)) { return true; }
            diagnostics.error(ErrorCode::E_TYPE,
                              "grammar operator '" + op + "' has an operand of the wrong sort");
            return false;
        };

        const H::Sort integer = H::Sort::integer();
        const H::Sort boolean = H::Sort::boolean();
        const H::Sort string = H::Sort::string();
        if (op == "str.++") {
            if (!arity(2, SIZE_MAX) || !expectArguments(string)) { return false; }
            result = string;
        } else if (op == "str.replace") {
            if (!arity(3, 3) || !expectArguments(string)) { return false; }
            result = string;
        } else if (op == "str.at") {
            if (!arity(2, 2)) { return false; }
            if (!H::sameSort(arguments[0], string)
                || !H::sameSort(arguments[1], integer)) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar str.at requires (String, Int)");
                return false;
            }
            result = string;
        } else if (op == "str.substr") {
            if (!arity(3, 3)) { return false; }
            if (!H::sameSort(arguments[0], string)
                || !H::sameSort(arguments[1], integer)
                || !H::sameSort(arguments[2], integer)) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar str.substr requires (String, Int, Int)");
                return false;
            }
            result = string;
        } else if (op == "str.len" || op == "str.to_int") {
            if (!arity(1, 1) || !expectArguments(string)) { return false; }
            result = integer;
        } else if (op == "str.from_int") {
            if (!arity(1, 1) || !expectArguments(integer)) { return false; }
            result = string;
        } else if (op == "str.indexof") {
            if (!arity(3, 3)) { return false; }
            if (!H::sameSort(arguments[0], string)
                || !H::sameSort(arguments[1], string)
                || !H::sameSort(arguments[2], integer)) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar str.indexof requires (String, String, Int)");
                return false;
            }
            result = integer;
        } else if (op == "str.contains" || op == "str.prefixof"
                   || op == "str.suffixof") {
            if (!arity(2, 2) || !expectArguments(string)) { return false; }
            result = boolean;
        } else if (op == "+" || op == "*") {
            if (!arity(2, SIZE_MAX) || !expectArguments(integer)) { return false; }
            result = integer;
        } else if (op == "-") {
            if (!arity(1, SIZE_MAX) || !expectArguments(integer)) { return false; }
            result = integer;
        } else if (op == "div" || op == "mod") {
            if (!arity(2, 2) || !expectArguments(integer)) { return false; }
            result = integer;
        } else if (op == "abs") {
            if (!arity(1, 1) || !expectArguments(integer)) { return false; }
            result = integer;
        } else if (op == "and" || op == "or" || op == "=>" || op == "xor") {
            if (!arity(2, SIZE_MAX) || !expectArguments(boolean)) { return false; }
            result = boolean;
        } else if (op == "not") {
            if (!arity(1, 1) || !expectArguments(boolean)) { return false; }
            result = boolean;
        } else if (op == "=" || op == "distinct") {
            if (!arity(2, SIZE_MAX)) { return false; }
            for (std::size_t i = 1; i < arguments.size(); ++i) {
                if (!H::sameSort(arguments[0], arguments[i])) {
                    diagnostics.error(ErrorCode::E_TYPE,
                                      "grammar equality operands have different sorts");
                    return false;
                }
            }
            result = boolean;
        } else if (op == "<" || op == "<=" || op == ">" || op == ">=") {
            if (!arity(2, SIZE_MAX) || !expectArguments(integer)) { return false; }
            result = boolean;
        } else if (op == "ite") {
            if (!arity(3, 3)) { return false; }
            if (!H::sameSort(arguments[0], boolean)
                || !H::sameSort(arguments[1], arguments[2])) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar ite requires a Boolean condition and equal branch sorts");
                return false;
            }
            result = arguments[1];
        } else if (op == "bvnot" || op == "bvneg") {
            if (!arity(1, 1) || arguments[0].kind != H::SortKind::BITVEC
                || !indices.empty()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar operator '" + op
                                      + "' requires one bit-vector operand");
                return false;
            }
            result = arguments[0];
        } else if (op == "bvand" || op == "bvor" || op == "bvxor"
                   || op == "bvnand" || op == "bvnor" || op == "bvxnor"
                   || op == "bvadd" || op == "bvsub" || op == "bvmul"
                   || op == "bvudiv" || op == "bvurem" || op == "bvsdiv"
                   || op == "bvsrem" || op == "bvsmod" || op == "bvshl"
                   || op == "bvlshr" || op == "bvashr") {
            const bool left_associative = op == "bvand" || op == "bvor"
                                          || op == "bvadd" || op == "bvmul";
            const bool matching_bitvectors = !arguments.empty()
                && arguments[0].kind == H::SortKind::BITVEC
                && std::all_of(arguments.begin() + 1, arguments.end(),
                               [&](const H::Sort& argument) {
                                   return H::sameSort(arguments[0], argument);
                               });
            if (!arity(2, left_associative ? SIZE_MAX : 2)
                || !matching_bitvectors || !indices.empty()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar operator '" + op
                                      + (left_associative
                                             ? " requires at least two equal-width bit-vector operands"
                                             : " requires exactly two equal-width bit-vector operands"));
                return false;
            }
            result = arguments[0];
        } else if (op == "bvult" || op == "bvule" || op == "bvugt"
                   || op == "bvuge" || op == "bvslt" || op == "bvsle"
                   || op == "bvsgt" || op == "bvsge") {
            if (!arity(2, 2) || arguments[0].kind != H::SortKind::BITVEC
                || !H::sameSort(arguments[0], arguments[1]) || !indices.empty()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar operator '" + op
                                      + "' requires equal-width bit-vector operands");
                return false;
            }
            result = boolean;
        } else if (op == "concat") {
            if (!arity(2, 2) || !indices.empty()
                || !std::all_of(arguments.begin(), arguments.end(), [](const H::Sort& arg) {
                       return arg.kind == H::SortKind::BITVEC;
                   })) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar concat requires exactly two bit-vector operands");
                return false;
            }
            unsigned width = 0;
            for (const H::Sort& argument : arguments) {
                if (argument.width > std::numeric_limits<unsigned>::max() - width) {
                    diagnostics.error(ErrorCode::E_RESOURCE,
                                      "grammar concat result width overflows unsigned range");
                    return false;
                }
                width += argument.width;
            }
            result = H::Sort::bitvec(width);
        } else if (op == "extract") {
            if (!arity(1, 1) || indices.size() != 2
                || arguments[0].kind != H::SortKind::BITVEC
                || indices[0] < indices[1] || indices[0] >= arguments[0].width) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar extract requires valid high/low indices for a bit-vector");
                return false;
            }
            result = H::Sort::bitvec(indices[0] - indices[1] + 1);
        } else if (op == "int2bv" || op == "int_to_bv") {
            if (!arity(1, 1) || indices.size() != 1
                || !H::sameSort(arguments[0], integer) || indices[0] == 0) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar int2bv requires one Int operand and a positive width");
                return false;
            }
            result = H::Sort::bitvec(indices[0]);
        } else if (op == "zero_extend" || op == "sign_extend"
                   || op == "repeat" || op == "rotate_left" || op == "rotate_right") {
            if (!arity(1, 1) || indices.size() != 1
                || arguments[0].kind != H::SortKind::BITVEC
                || (op == "repeat" && indices[0] == 0)) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar indexed bit-vector operator has invalid indices/operand");
                return false;
            }
            unsigned width = arguments[0].width;
            if (op == "zero_extend" || op == "sign_extend") {
                if (indices[0] > std::numeric_limits<unsigned>::max() - width) {
                    diagnostics.error(ErrorCode::E_RESOURCE,
                                      "grammar extension result width overflows unsigned range");
                    return false;
                }
                width += indices[0];
            } else if (op == "repeat") {
                if (indices[0] > std::numeric_limits<unsigned>::max() / width) {
                    diagnostics.error(ErrorCode::E_RESOURCE,
                                      "grammar repeat result width overflows unsigned range");
                    return false;
                }
                width *= indices[0];
            }
            result = H::Sort::bitvec(width);
        } else if (op == "bvcomp") {
            if (!arity(2, 2) || arguments[0].kind != H::SortKind::BITVEC
                || !H::sameSort(arguments[0], arguments[1]) || !indices.empty()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar bvcomp requires equal-width bit-vector operands");
                return false;
            }
            result = H::Sort::bitvec(1);
        } else if (op == "bv2int" || op == "bv2nat"
                   || op == "ubv_to_int" || op == "sbv_to_int") {
            if (!arity(1, 1) || arguments[0].kind != H::SortKind::BITVEC
                || !indices.empty()) {
                diagnostics.error(ErrorCode::E_TYPE,
                                  "grammar " + op + " requires one bit-vector operand");
                return false;
            }
            result = integer;
        } else {
            // A previously declared nonrecursive helper is a grammar symbol,
            // not a new unrestricted synthesis function. Keep its application
            // in the candidate and its definition in the target environment.
            for (std::size_t i = 0; i < definitions_.size(); ++i) {
                if (definitions_[i].list[1].atom != op
                    || definition_command_indices_[i] >= active_function_command_index_
                    || !indices.empty()) { continue; }
                const auto& parameters = definition_parameters_[i];
                if (!arity(parameters.size(), parameters.size())) { return false; }
                for (std::size_t j = 0; j < parameters.size(); ++j) {
                    if (!H::sameSort(arguments[j], parameters[j].hir_sort)) {
                        diagnostics.error(ErrorCode::E_TYPE,
                                          "grammar helper '" + op + "' has an operand of the wrong sort");
                        return false;
                    }
                }
                std::string ignored;
                return sort(definitions_[i].list[3], ignored, result, diagnostics);
            }
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "unsupported grammar operator '" + op + "'");
            return false;
        }
        return true;
    }

    const Nonterminal* nonterminal(const std::string& name) const {
        const auto found = nonterminal_indices_.find(name);
        return found == nonterminal_indices_.end()
                   ? nullptr : &nonterminals_[found->second];
    }

    std::vector<std::string> expand(const Sexp& expression, unsigned depth,
                                    Uir::Diagnostics& diagnostics) {
        if (expression.isAtom()) {
            if (expression.isStringLiteral()) { return {printSexp(expression)}; }
            if (nonterminal(expression.atom) != nullptr) {
                if (depth == 0) { return {}; }
                return terms(expression.atom, depth - 1, diagnostics);
            }
            if (!expression.quoted_symbol && legacyNegativeInteger(expression.atom)
                && !declaredGrammarSymbol(expression.atom)) {
                return {"(- " + expression.atom.substr(1) + ")"};
            }
            return {printSexp(expression)};
        }
        if (expression.head() == "Constant") {
            if (expression.list.size() != 2) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed (Constant Sort) grammar term");
                return {};
            }
            std::string constant_sort;
            H::Sort constant_hir;
            if (!sort(expression.list[1], constant_sort, constant_hir, diagnostics)) {
                return {};
            }
            if (constant_sort == "Int") { return {hole_marker_}; }
            if (constant_sort == "Bool") { return {"false", "true"}; }
            if (constant_hir.kind == H::SortKind::BITVEC) {
                const std::string marker = hole_marker_ + "bv"
                                         + std::to_string(constant_hir.width) + "x";
                hole_marker_widths_[marker] = constant_hir.width;
                return {marker};
            }
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "(Constant " + constant_sort
                                  + ") requires typed grammar-hole support");
            return {};
        }
        if (expression.head() == "Variable") {
            if (expression.list.size() != 2) {
                diagnostics.error(ErrorCode::E_PARSE,
                                  "malformed (Variable Sort) grammar term");
                return {};
            }
            std::string wanted;
            H::Sort wanted_hir;
            if (!sort(expression.list[1], wanted, wanted_hir, diagnostics)) { return {}; }
            std::vector<std::string> result;
            for (const Typed& parameter : parameters_) {
                if (H::sameSort(parameter.hir_sort, wanted_hir)) {
                    result.push_back(renderSymbol(parameter.name));
                }
            }
            return result;
        }
        if (expression.head() == "let" || expression.head() == "!") {
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "grammar let/weighted annotations need scope and weight tracking");
            return {};
        }
        if (expression.list.empty()) { return {"()"}; }

        std::vector<std::vector<std::string>> children;
        for (const Sexp& child : expression.list) {
            auto alternatives = expand(child, depth, diagnostics);
            if (diagnostics.hasErrors() || alternatives.empty()) { return {}; }
            children.push_back(std::move(alternatives));
        }
        std::vector<std::string> result{std::string{}};
        for (const auto& alternatives : children) {
            std::vector<std::string> next;
            for (const std::string& prefix : result) {
                for (const std::string& alternative : alternatives) {
                    next.push_back(prefix.empty() ? alternative
                                                  : prefix + " " + alternative);
                    if (next.size() > CANDIDATE_LIMIT) {
                        diagnostics.error(ErrorCode::E_RESOURCE,
                                          "SyGuS grammar product exceeds the candidate limit");
                        return {};
                    }
                }
            }
            result = std::move(next);
        }
        for (std::string& item : result) { item = "(" + item + ")"; }
        return result;
    }

    std::vector<std::string> terms(const std::string& name, unsigned depth,
                                   Uir::Diagnostics& diagnostics) {
        const std::string key = name + "#" + std::to_string(depth);
        const auto cached = memo_.find(key);
        if (cached != memo_.end()) { return cached->second; }
        const Nonterminal* nt = nonterminal(name);
        if (!nt) {
            diagnostics.error(ErrorCode::E_TYPE,
                              "grammar references undeclared nonterminal '" + name + "'");
            return {};
        }
        std::set<std::string> unique;
        for (const Sexp& rule : nt->rules) {
            auto expanded = expand(rule, depth, diagnostics);
            unique.insert(expanded.begin(), expanded.end());
            if (diagnostics.hasErrors()) { return {}; }
            if (unique.size() > CANDIDATE_LIMIT) {
                diagnostics.error(ErrorCode::E_RESOURCE,
                                  "SyGuS grammar derives more than "
                                      + std::to_string(CANDIDATE_LIMIT)
                                      + " terms at the requested depth");
                return {};
            }
        }
        std::vector<std::string> result(unique.begin(), unique.end());
        memo_.emplace(key, result);
        return result;
    }

    Sexp instantiate(const Sexp& expression,
                     const std::map<std::string, Sexp>& actuals) const {
        if (expression.isStringLiteral()) { return expression; }
        if (expression.isAtom()) {
            const auto found = actuals.find(expression.atom);
            return found == actuals.end() ? expression : found->second;
        }
        Sexp result;
        for (const Sexp& child : expression.list) {
            result.list.push_back(instantiate(child, actuals));
        }
        return result;
    }

    void canonicalizeLegacyStringOperators(Sexp& expression) const {
        if (expression.isAtom()) { return; }
        for (Sexp& child : expression.list) {
            canonicalizeLegacyStringOperators(child);
        }
        if (expression.list.empty() || !expression.list.front().isAtom()) { return; }
        std::string& op = expression.list.front().atom;
        if (op == "int.to.str" && isBuiltinInSourceLogic(op)) {
            op = "str.from_int";
        } else if (op == "str.to.int" && isBuiltinInSourceLogic(op)) {
            op = "str.to_int";
        }
    }

    Sexp renameSynthReferences(
        const Sexp& expression, const std::map<std::string, std::string>& wrappers,
        const std::set<std::string>& shadowed,
        const std::map<std::string, std::string>& helpers = {}) const {
        if (expression.isStringLiteral()) { return expression; }
        if (expression.isAtom()) {
            const auto wrapper = wrappers.find(expression.atom);
            if (wrapper != wrappers.end() && shadowed.count(expression.atom) == 0) {
                return symbolSexp(wrapper->second);
            }
            const auto helper = helpers.find(expression.atom);
            if (helper != helpers.end() && shadowed.count(expression.atom) == 0) {
                return symbolSexp(helper->second);
            }
            return expression;
        }
        if (expression.list.empty()) { return expression; }
        if ((expression.head() == "forall" || expression.head() == "exists"
             || expression.head() == "lambda")
            && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            Sexp result;
            result.list.push_back(expression.list[0]);
            result.list.push_back(expression.list[1]);
            std::set<std::string> nested = shadowed;
            for (const Sexp& entry : expression.list[1].list) {
                if (entry.list.size() == 2 && entry.list[0].isAtom()) {
                    nested.insert(entry.list[0].atom);
                }
            }
            result.list.push_back(renameSynthReferences(
                expression.list[2], wrappers, nested, helpers));
            return result;
        }
        if (expression.head() == "let" && expression.list.size() == 3
            && !expression.list[1].isAtom()) {
            Sexp result;
            result.list.push_back(expression.list[0]);
            Sexp bindings;
            std::set<std::string> nested = shadowed;
            for (const Sexp& entry : expression.list[1].list) {
                if (entry.list.size() == 2 && entry.list[0].isAtom()) {
                    bindings.list.push_back(form({entry.list[0], renameSynthReferences(
                        entry.list[1], wrappers, shadowed, helpers)}));
                    nested.insert(entry.list[0].atom);
                } else {
                    bindings.list.push_back(entry);
                }
            }
            result.list.push_back(std::move(bindings));
            result.list.push_back(renameSynthReferences(
                expression.list[2], wrappers, nested, helpers));
            return result;
        }
        Sexp result;
        result.list.reserve(expression.list.size());
        for (std::size_t i = 0; i < expression.list.size(); ++i) {
            if (i == 0 && expression.list[i].isAtom()) {
                if (expression.list[i].isStringLiteral()) {
                    result.list.push_back(expression.list[i]);
                    continue;
                }
                const auto wrapper = wrappers.find(expression.list[i].atom);
                if (wrapper != wrappers.end()
                    && shadowed.count(expression.list[i].atom) == 0) {
                    // A nullary synth-fun is an SMT constant. The source may
                    // spell its reference as `(fb)`, but the renamed target
                    // must use the declared wrapper symbol bare; `(wrapper)`
                    // is a zero-argument application, which SMT-LIB does not
                    // admit. Keep non-nullary wrappers as ordinary calls.
                    if (expression.list.size() == 1
                        && isNullarySynthFunction(expression.list[i].atom)) {
                        return symbolSexp(wrapper->second);
                    }
                    result.list.push_back(symbolSexp(wrapper->second));
                    continue;
                }
                const auto helper = helpers.find(expression.list[i].atom);
                if (helper != helpers.end()
                    && shadowed.count(expression.list[i].atom) == 0) {
                    // define-fun helpers can also be nullary constants. The
                    // same S-expression normalization applies when a helper
                    // call is rewritten in constraints or candidate terms.
                    if (expression.list.size() == 1
                        && isNullaryHelper(expression.list[i].atom)) {
                        return symbolSexp(helper->second);
                    }
                    result.list.push_back(symbolSexp(helper->second));
                    continue;
                }
            }
            result.list.push_back(renameSynthReferences(expression.list[i], wrappers,
                                                        shadowed, helpers));
        }
        return result;
    }

    bool isNullarySynthFunction(const std::string& name) const {
        const auto found = std::find_if(
            synth_functions_.begin(), synth_functions_.end(),
            [&](const SynthFunction& function) { return function.name == name; });
        return found != synth_functions_.end() && found->parameters.empty();
    }

    bool isNullaryHelper(const std::string& name) const {
        for (std::size_t i = 0; i < definitions_.size(); ++i) {
            if (definitions_[i].list.size() >= 4
                && definitions_[i].list[1].isAtom()
                && definitions_[i].list[1].atom == name
                && i < definition_parameters_.size()
                && definition_parameters_[i].empty()) {
                return true;
            }
        }
        return false;
    }

    bool renameHelperCalls(const std::string& text,
                           const std::map<std::string, std::string>& helpers,
                           const std::set<std::string>& shadowed,
                           std::string& result,
                           Uir::Diagnostics& diagnostics,
                           const std::map<std::string, std::string>& wrappers = {}) const {
        std::vector<Sexp> roots;
        std::string error;
        SexpReader reader(text);
        if (!reader.readAll(roots, error) || roots.size() != 1) {
            diagnostics.error(ErrorCode::E_INTERNAL,
                              "generated SyGuS candidate cannot be reparsed for helper renaming");
            return false;
        }
        canonicalizeLegacyStringOperators(roots.front());
        result = printSexp(closeExpression(
            renameSynthReferences(roots.front(), wrappers, shadowed, helpers), shadowed));
        return true;
    }

    Sexp substituteFunctionScoped(
        const Sexp& expression, const Sexp& candidate, bool& ok,
        const std::set<std::string>& shadowed,
        const std::map<std::string, std::string>& helper_renames) const {
        if (expression.isStringLiteral()) { return expression; }
        if (expression.isAtom()) {
            if (shadowed.count(expression.atom) != 0) { return expression; }
            const auto renamed = helper_renames.find(expression.atom);
            if (renamed != helper_renames.end()) { return symbolSexp(renamed->second); }
            if (expression.atom == function_name_) {
                if (!parameters_.empty()) { ok = false; }
                // Nullary synth-fun calls are atoms in SMT-LIB. Their selected
                // grammar term still needs the same target-only helper aliases
                // as candidates inserted at an application site.
                return renameSynthReferences(candidate, {}, shadowed, helper_renames);
            }
            return expression;
        }
        if (expression.head() == function_name_
            && shadowed.count(function_name_) == 0) {
            if (expression.list.size() != parameters_.size() + 1) {
                ok = false;
                return expression;
            }
            std::map<std::string, Sexp> actuals;
            for (std::size_t i = 0; i < parameters_.size(); ++i) {
                actuals.emplace(parameters_[i].name,
                                substituteFunctionScoped(expression.list[i + 1], candidate,
                                                          ok, shadowed, helper_renames));
            }
            const Sexp instantiated = instantiate(candidate, actuals);
            return substituteFunctionScoped(instantiated, candidate, ok, shadowed,
                                            helper_renames);
        }
        Sexp result;
        if ((expression.head() == "forall" || expression.head() == "exists"
             || expression.head() == "lambda")
            && expression.list.size() == 3 && !expression.list[1].isAtom()) {
            result.list.push_back(expression.list[0]);
            result.list.push_back(expression.list[1]);
            std::set<std::string> nested = shadowed;
            for (const Sexp& entry : expression.list[1].list) {
                if (entry.list.size() == 2 && entry.list[0].isAtom()) {
                    nested.insert(entry.list[0].atom);
                }
            }
            result.list.push_back(substituteFunctionScoped(
                expression.list[2], candidate, ok, nested, helper_renames));
            return result;
        }
        if (expression.head() == "let" && expression.list.size() == 3
            && !expression.list[1].isAtom()) {
            result.list.push_back(expression.list[0]);
            Sexp bindings;
            std::set<std::string> nested = shadowed;
            for (const Sexp& entry : expression.list[1].list) {
                if (entry.list.size() == 2 && entry.list[0].isAtom()) {
                    bindings.list.push_back(form({
                        entry.list[0],
                        substituteFunctionScoped(entry.list[1], candidate, ok,
                                                  shadowed, helper_renames)}));
                    nested.insert(entry.list[0].atom);
                } else {
                    bindings.list.push_back(entry);
                }
            }
            result.list.push_back(std::move(bindings));
            result.list.push_back(substituteFunctionScoped(
                expression.list[2], candidate, ok, nested, helper_renames));
            return result;
        }
        for (std::size_t i = 0; i < expression.list.size(); ++i) {
            if (i == 0 && expression.list[i].isAtom()) {
                if (expression.list[i].isStringLiteral()) {
                    result.list.push_back(expression.list[i]);
                    continue;
                }
                const auto renamed = helper_renames.find(expression.list[i].atom);
                if (renamed != helper_renames.end()
                    && shadowed.count(expression.list[i].atom) == 0) {
                    result.list.push_back(symbolSexp(renamed->second));
                    continue;
                }
            }
            result.list.push_back(substituteFunctionScoped(
                expression.list[i], candidate, ok, shadowed, helper_renames));
        }
        return result;
    }

    Sexp substituteFunction(
        const Sexp& expression, const Sexp& candidate, bool& ok,
        const std::map<std::string, std::string>& helper_renames = {},
        const std::set<std::string>& initially_shadowed = {}) const {
        return substituteFunctionScoped(expression, candidate, ok,
                                        initially_shadowed, helper_renames);
    }

    static std::string binder(const std::vector<Typed>& variables) {
        std::string result = "(";
        for (std::size_t i = 0; i < variables.size(); ++i) {
            if (i != 0) { result += " "; }
            result += "(" + renderSymbol(variables[i].name) + " "
                    + variables[i].sort + ")";
        }
        return result + ")";
    }

    static std::string quantify(const std::string& variables,
                                const std::string& body) {
        return variables == "()" ? body : "(forall " + variables + " " + body + ")";
    }

    static std::string conjoin(const std::vector<std::string>& terms) {
        if (terms.empty()) { return "true"; }
        if (terms.size() == 1) { return terms.front(); }
        std::string result = "(and";
        for (const std::string& term : terms) { result += " " + term; }
        return result + ")";
    }

    static std::string join(const std::vector<std::string>& terms,
                            const std::string& separator) {
        std::string result;
        for (const std::string& term : terms) {
            if (!result.empty()) { result += separator; }
            result += term;
        }
        return result;
    }

    std::string defineFun(const std::string& body) const {
        return "(define-fun " + renderSymbol(function_name_) + " " + binder(parameters_)
             + " " + return_sort_ + " " + body + ")";
    }

    std::string defineFun(const SynthFunction& function, const std::string& body) const {
        return "(define-fun " + renderSymbol(function.name) + " "
             + binder(function.parameters)
             + " " + function.return_sort + " " + body + ")";
    }

    std::string source_;
    std::string file_;
    unsigned depth_ = 0;
    std::vector<Sexp> commands_;
    std::vector<SynthFunction> synth_functions_;
    std::set<std::string> synth_names_;
    std::size_t command_index_ = 0;
    std::size_t active_function_command_index_ = 0;
    std::string function_name_;
    std::string logic_name_;
    std::string default_nt_prefix_;
    bool default_grammar_requested_ = false;
    std::string hole_marker_;
    std::string hole_prefix_;
    std::map<std::string, unsigned> hole_marker_widths_;
    std::set<std::string> definition_names_;
    std::vector<Sexp> definitions_;
    std::vector<std::vector<Typed>> definition_parameters_;
    std::vector<bool> definition_after_synth_;
    std::vector<std::size_t> definition_command_indices_;
    std::vector<std::set<std::string>> definition_visible_synths_;
    std::vector<std::set<std::string>> definition_visible_universals_;
    std::vector<bool> definition_dependent_;
    std::vector<std::vector<std::size_t>> definition_global_indices_;
    std::vector<std::vector<std::vector<std::size_t>>> candidate_definition_global_indices_;
    const std::vector<std::vector<std::size_t>>* active_candidate_definition_globals_ = nullptr;
    std::map<std::string, std::size_t> definition_indices_;
    std::map<std::string, std::size_t> closure_definition_targets_;
    std::map<std::string, std::string> source_helper_targets_;
    std::string unbounded_candidate_;
    std::string unbounded_prelude_;
    std::map<std::string, std::string> unbounded_synth_wrappers_;
    std::string unbounded_source_term_placeholder_;
    std::string unbounded_source_term_symbol_;
    bool unbounded_grammar_ = false;
    std::vector<std::string> unbounded_eval_parameter_names_;
    std::string return_sort_;
    H::Sort return_hir_sort_ = H::Sort::boolean();
    std::vector<Typed> parameters_;
    std::vector<Typed> universal_variables_;
    std::vector<Typed> target_universal_variables_;
    std::map<std::string, std::size_t> universal_indices_;
    std::map<std::string, std::string> universal_aliases_;
    Sexp grammar_declarations_;
    Sexp grammar_rules_;
    std::vector<Nonterminal> nonterminals_;
    std::vector<Sexp> constraints_;
    std::vector<Sexp> invariant_constraints_;
    bool invariant_mode_ = false;
    std::map<std::string, std::vector<std::string>> memo_;
    std::map<std::string, std::size_t> estimate_memo_;
    std::map<std::string, std::size_t> nonterminal_indices_;
    std::size_t estimate_work_ = 0;
    bool estimate_budget_exceeded_ = false;
    std::vector<std::vector<S::ChoiceAlternative::Binding>> candidate_bindings_;

    std::vector<std::string> candidate_targets_;
    std::vector<std::map<std::string, std::string>> candidate_helper_renames_;
    std::vector<std::vector<Sexp>> candidate_helper_definitions_;
    S::ChoiceObservable definition_choice_;
    S::ModelProjection projection_;
    S::Signature source_signature_;
    std::vector<S::SymbolMapping> symbol_map_;
    std::vector<S::Sentence> target_axioms_;
};

bool parseDepth(const Uir::ParamMap& options, unsigned& depth,
                Uir::Diagnostics& diagnostics) {
    const auto found = options.find("grammar_depth");
    if (found == options.end()) {
        diagnostics.error(
            ErrorCode::E_UNSUPPORTED_CONSTRUCT,
            "no grammar_depth: pass `grammar_depth=<d>`; bounded synthesis has no "
            "sound completeness claim without an explicit GRAMMAR_RESTRICTION");
        return false;
    }
    const std::string& text = found->second;
    if (text.empty()
        || !std::all_of(text.begin(), text.end(),
                        [](unsigned char c) { return std::isdigit(c) != 0; })) {
        diagnostics.error(ErrorCode::E_PARSE,
                          "grammar_depth must be a non-negative decimal integer");
        return false;
    }
    unsigned long long value = 0;
    try {
        value = std::stoull(text);
    } catch (const std::exception&) {
        diagnostics.error(ErrorCode::E_PARSE, "grammar_depth is outside integer range");
        return false;
    }
    if (value > UINT_MAX) {
        diagnostics.error(ErrorCode::E_PARSE,
                          "grammar_depth exceeds the frontend's supported range");
        return false;
    }
    depth = static_cast<unsigned>(value);
    return true;
}

bool parseGrammarMode(const Uir::ParamMap& options, unsigned& depth,
                      bool& unbounded, Uir::Diagnostics& diagnostics) {
    const auto mode = options.find("grammar_mode");
    const auto depth_option = options.find("grammar_depth");
    if (mode == options.end()) {
        // Keep the former explicit-depth API stable. Omitting both options
        // selects the finite-tree encoding without a depth restriction.
        unbounded = depth_option == options.end();
        if (unbounded) { depth = 0; return true; }
        return parseDepth(options, depth, diagnostics);
    }
    if (mode->second == "unbounded") {
        if (depth_option != options.end()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "grammar_mode=unbounded cannot be combined with grammar_depth");
            return false;
        }
        unbounded = true;
        depth = 0;
        return true;
    }
    if (mode->second == "bounded") {
        if (depth_option == options.end()) {
            diagnostics.error(ErrorCode::E_PARSE,
                              "grammar_mode=bounded requires grammar_depth=<d>");
            return false;
        }
        unbounded = false;
        return parseDepth(options, depth, diagnostics);
    }
    diagnostics.error(ErrorCode::E_PARSE,
                      "grammar_mode must be 'bounded' or 'unbounded'");
    return false;
}

class SygusLanguage : public Language {
public:
    SygusLanguage() {
        coverage_.total = 2;
        coverage_.supported = 1;
        coverage_.missing = {
            "weighted grammars, assumes, oracles, and Constant sorts "
            "other than Bool/Int/BitVec/String in unbounded mode",
        };
    }

    std::string id() const override { return "sygus"; }
    std::string displayName() const override {
        return "SyGuS-IF 2.1 (bounded and unbounded explicit grammar core)";
    }
    std::string version() const override {
        return "2.1 finite grammar AST/evaluator and explicit bounded core";
    }
    std::vector<std::string> extensions() const override { return {".sl"}; }
    const OpCoverage& coverage() const override { return coverage_; }

    double sniff(std::string_view head) const override {
        return head.find("synth-fun") != std::string_view::npos
                   || head.find("synth-inv") != std::string_view::npos
                   || (head.find("set-logic") != std::string_view::npos
                       && head.find("constraint") != std::string_view::npos)
               ? 0.9 : 0.0;
    }

    ParseOutcome parse(const SourceUnit& unit, const ParseOptions& options) override {
        ParseOutcome result;
        std::string source = unit.inline_source;
        if (source.empty()) {
            std::error_code error;
            if (std::filesystem::is_directory(unit.main_path, error)) {
                result.diagnostics.error(ErrorCode::E_IO,
                                         "'" + unit.main_path + "' is a directory");
                return result;
            }
            std::ifstream input(unit.main_path, std::ios::binary);
            if (!input) {
                result.diagnostics.error(ErrorCode::E_IO,
                                         "cannot open '" + unit.main_path + "'");
                return result;
            }
            std::ostringstream buffer;
            buffer << input.rdbuf();
            source = buffer.str();
        }
        if (source.find("synth-fun") == std::string::npos
            && source.find("synth-inv") == std::string::npos) {
            result.diagnostics.error(ErrorCode::E_PARSE,
                                     "no synth-fun: this is not a SyGuS-IF file");
            return result;
        }
        unsigned depth = 0;
        bool unbounded = false;
        if (!parseGrammarMode(options.options, depth, unbounded, result.diagnostics)) {
            return result;
        }

        const std::string name = unit.main_path.empty() ? unit.display_name
                                                         : unit.main_path;
        try {
            SygusParser parser(source, name, depth, unbounded);
            result.model = parser.parse(result.diagnostics, result.report);
            if (result.model) {
                result.semantics.add(S::sygusToRelationalContract(
                    *result.model, result.report.fidelity(), parser.projection(),
                    parser.sourceSignature(), parser.symbolMap(), parser.targetAxioms()));
            }
        } catch (const std::exception& error) {
            result.model.reset();
            result.diagnostics.error(ErrorCode::E_INTERNAL,
                                     std::string("sygus frontend: ") + error.what());
        }
        return result;
    }

private:
    OpCoverage coverage_;
};

} // namespace

LanguagePtr mkSygusLanguage() { return std::make_shared<SygusLanguage>(); }

} // namespace SOMTParser::Lang
