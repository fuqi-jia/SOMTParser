/* -*- Source -*-
 * Semantic configuration and typed relational expression construction.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/translation/semantics.h"
#include "somtparser/hir/soft_objectives.h"
#include "somtparser/core/util.h"
#include "somtparser/hir/typecheck.h"

#include <algorithm>
#include <limits>
#include <stdexcept>
#include <cctype>
#include <exception>
#include <map>
#include <set>
#include <string_view>
#include <tuple>
#include <unordered_set>
#include <utility>

namespace SOMTParser::Uir::Sem {

namespace H = Hir;

namespace {

bool compactNumericBound(const H::ExprPtr& bound, const H::Sort& sort) {
    if (!bound) { return true; }
    if (sort.kind != H::SortKind::INT && sort.kind != H::SortKind::REAL) { return false; }
    // Bounds are comparisons, not assignments. In particular, MPS explicit
    // integer bounds are Real literals, and 0.5 <= an Int variable is legal.
    // Preserve the exact endpoint; materialization keeps numeric promotion
    // identical to the ordinary comparison instead of rounding the bound.
    return (bound->kind == H::ExprKind::LIT_INT && bound->sort.kind == H::SortKind::INT)
        || (bound->kind == H::ExprKind::LIT_REAL && bound->sort.kind == H::SortKind::REAL);
}

bool validDeclarationBounds(const DeclarationBoundsAxiom& axiom,
                            const SignatureSnapshot& signature) {
    if (axiom.target_symbol_index >= signature.symbols.size()
        || (!axiom.lower_bound && !axiom.upper_bound)) { return false; }
    const auto& symbol = signature.symbols[axiom.target_symbol_index];
    return symbol.name == axiom.target_name
        && symbol.kind == SymbolKind::CONSTANT && symbol.domain.empty()
        && (symbol.codomain.kind == H::SortKind::INT
            || symbol.codomain.kind == H::SortKind::REAL)
        && compactNumericBound(axiom.lower_bound, symbol.codomain)
        && compactNumericBound(axiom.upper_bound, symbol.codomain);
}

bool isBoolLiteral(const H::ExprPtr& e, bool value) {
    return e && e->kind == H::ExprKind::LIT_BOOL && e->bool_value == value;
}

const ProofObligation* findObligation(const TranslationContract& contract,
                                      ProofObligationKind kind) {
    for (const ProofObligation& obligation : contract.obligations) {
        if (obligation.kind == kind) { return &obligation; }
    }
    return nullptr;
}

bool hasRecordedEvidence(const ProofObligation* obligation) {
    return obligation && obligation->evidence != EvidenceKind::PENDING
           && !obligation->rationale.empty();
}

bool hasRecordedCountEvidence(const ProofObligation* obligation) {
    if (!hasRecordedEvidence(obligation)) { return false; }
    if (obligation->evidence != EvidenceKind::BY_CONSTRUCTION
        && obligation->evidence != EvidenceKind::TESTED
        && obligation->evidence != EvidenceKind::MACHINE_CHECKED) {
        return false;
    }
    for (const std::string& reference : obligation->evidence_refs) {
        if (!reference.empty()) { return true; }
    }
    return false;
}

template <class SignatureLike>
std::vector<const Symbol*> symbolsNamed(const SignatureLike& signature,
                                        const std::string& name) {
    std::vector<const Symbol*> found;
    for (const Symbol& symbol : signature.symbols) {
        if (symbol.name == name) { found.push_back(&symbol); }
    }
    return found;
}

// A sorted non-owning index keeps duplicate declarations visible without one
// tree node, copied name, and separately allocated vector per source symbol.
// The signatures outlive validation and cannot mutate during this lookup.
using SymbolIndex = std::vector<const Symbol*>;
struct SymbolRange {
    SymbolIndex::const_iterator first;
    SymbolIndex::const_iterator last;
    bool empty() const { return first == last; }
    std::size_t size() const { return static_cast<std::size_t>(last - first); }
    const Symbol* front() const { return *first; }
    const Symbol* operator[](std::size_t index) const { return first[index]; }
    auto begin() const { return first; }
    auto end() const { return last; }
};

template <class SignatureLike>
SymbolIndex indexSymbols(const SignatureLike& signature) {
    SymbolIndex index;
    index.reserve(signature.symbols.size());
    for (const Symbol& symbol : signature.symbols) { index.push_back(&symbol); }
    std::stable_sort(index.begin(), index.end(),
        [](const Symbol* left, const Symbol* right) {
            return left->name < right->name;
        });
    return index;
}

SymbolRange lookup(const SymbolIndex& index, const std::string& name) {
    const auto first = std::lower_bound(index.begin(), index.end(), name,
        [](const Symbol* symbol, const std::string& wanted) {
            return symbol->name < wanted;
        });
    const auto last = std::upper_bound(first, index.end(), name,
        [](const std::string& wanted, const Symbol* symbol) {
            return wanted < symbol->name;
        });
    return {first, last};
}

const H::Sort* mappedSort(const TranslationContract& contract,
                          const H::Sort& source) {
    const H::Sort* found = nullptr;
    for (const SortMapping& mapping : contract.sort_map) {
        if (!H::sameSort(mapping.source, source)) { continue; }
        if (found != nullptr && !H::sameSort(*found, mapping.target)) {
            return nullptr;
        }
        found = &mapping.target;
    }
    return found;
}

bool symbolTypesMap(const TranslationContract& contract, const Symbol& source,
                    const Symbol& target) {
    if (source.kind != target.kind || source.domain.size() != target.domain.size()) {
        return false;
    }
    for (std::size_t i = 0; i < source.domain.size(); ++i) {
        const H::Sort* mapped = mappedSort(contract, source.domain[i]);
        if (mapped == nullptr || !H::sameSort(*mapped, target.domain[i])) {
            return false;
        }
    }
    const H::Sort* result = mappedSort(contract, source.codomain);
    return result != nullptr && H::sameSort(*result, target.codomain);
}

bool namedSymbolsMap(const TranslationContract& contract,
                     const SymbolRange& source,
                     const SymbolRange& target) {
    if (source.empty() || target.empty()) { return false; }

    std::vector<bool> used(target.size(), false);
    for (const Symbol* source_symbol : source) {
        std::size_t match = target.size();
        for (std::size_t i = 0; i < target.size(); ++i) {
            if (used[i] || !symbolTypesMap(contract, *source_symbol, *target[i])) {
                continue;
            }
            if (match != target.size()) {
                // Two target symbols with the same namespace and type cannot
                // be distinguished by this mapping.
                return false;
            }
            match = i;
        }
        if (match == target.size()) { return false; }
        used[match] = true;
    }
    return true;
}

bool sameSymbolType(const Symbol& left, const Symbol& right) {
    if (left.kind != right.kind || left.domain.size() != right.domain.size()
        || !H::sameSort(left.codomain, right.codomain)) {
        return false;
    }
    for (std::size_t i = 0; i < left.domain.size(); ++i) {
        if (!H::sameSort(left.domain[i], right.domain[i])) { return false; }
    }
    return true;
}

bool sameInstitutionDefinition(const Institution& left, const Institution& right) {
    const AssumptionProfile& a = left.assumptions;
    const AssumptionProfile& b = right.assumptions;
    return left.id == right.id
        && left.surface_language == right.surface_language
        && left.object_logic == right.object_logic
        && left.meta_logic == right.meta_logic
        && left.sentence_space == right.sentence_space
        && left.model_class == right.model_class
        && left.satisfaction_relation == right.satisfaction_relation
        && a.id == b.id
        && a.carriers == b.carriers
        && a.carrier_emptiness == b.carrier_emptiness
        && a.functions == b.functions
        && a.undefined == b.undefined
        && a.arithmetic == b.arithmetic
        && a.overflow == b.overflow
        && a.division == b.division
        && a.arrays == b.arrays
        && a.equality == b.equality
        && a.quantifiers == b.quantifiers
        && a.invalid_phase == b.invalid_phase
        && a.annotations == b.annotations;
}

bool sameSignature(const SignatureSnapshot& left,
                   const SignatureSnapshot& right) {
    if (left.symbols.size() != right.symbols.size()
        || left.sort_constructors.size() != right.sort_constructors.size()
        || left.symbol_ranges.size() != right.symbol_ranges.size()) {
        return false;
    }
    // A compact range is part of the signature just as each expanded symbol
    // would be. Compare complete range descriptors without materializing its
    // potentially millions of names; declaration order is immaterial.
    using RangeKey = std::tuple<std::string, std::string, std::uint64_t, std::uint64_t>;
    std::map<RangeKey, const SymbolPatternRange*> right_ranges;
    for (const auto& range : right.symbol_ranges) {
        if (!right_ranges.emplace(
                RangeKey{range.prefix, range.suffix, range.first, range.count}, &range).second) {
            return false;
        }
    }
    for (const auto& range : left.symbol_ranges) {
        const auto found = right_ranges.find({range.prefix, range.suffix, range.first, range.count});
        if (found == right_ranges.end()) { return false; }
        const auto& other = *found->second;
        if (range.kind != other.kind || range.domain.size() != other.domain.size()
            || !H::sameSort(range.codomain, other.codomain)) {
            return false;
        }
        for (std::size_t i = 0; i < range.domain.size(); ++i) {
            if (!H::sameSort(range.domain[i], other.domain[i])) { return false; }
        }
        right_ranges.erase(found);
    }
    // Like term symbols, free sort constructors are a namespace-level set for
    // signature compatibility. Keep source order in the descriptor, but do
    // not make declaration order itself a semantic mismatch.
    std::map<std::string, std::size_t> right_sorts;
    for (const SortConstructor& sort : right.sort_constructors) {
        if (!right_sorts.emplace(sort.name, sort.arity).second) { return false; }
    }
    for (const SortConstructor& sort : left.sort_constructors) {
        const auto it = right_sorts.find(sort.name);
        if (it == right_sorts.end() || it->second != sort.arity) { return false; }
        right_sorts.erase(it);
    }
    if (!right_sorts.empty()) { return false; }

    // Grouped by name before matching. The inner test begins `source.name !=
    // right.symbols[i].name`, so a pair with different names can never match
    // -- yet the loop visited all n of them for each of the n on the left,
    // spending quadratic time to discover in the cheapest field that almost
    // every pair was irrelevant. A direct frontend's signature is one symbol
    // per declared variable, so n is the size of the model, and this is
    // called once per stage transition on every translation.
    //
    // The rule is unchanged, including its ambiguity clause: a left symbol
    // matching two unmatched right symbols is still a failure, because only
    // candidates of the same name could ever have matched.
    std::map<std::string, std::vector<std::size_t>> by_name;
    for (std::size_t i = 0; i < right.symbols.size(); ++i) {
        by_name[right.symbols[i].name].push_back(i);
    }

    std::vector<bool> matched(right.symbols.size(), false);
    for (const Symbol& source : left.symbols) {
        const auto candidates = by_name.find(source.name);
        if (candidates == by_name.end()) { return false; }
        std::size_t match = right.symbols.size();
        for (const std::size_t i : candidates->second) {
            if (matched[i] || !sameSymbolType(source, right.symbols[i])) {
                continue;
            }
            if (match != right.symbols.size()) { return false; }
            match = i;
        }
        if (match == right.symbols.size()) { return false; }
        matched[match] = true;
    }
    return true;
}

template <class SignatureLike>
bool signatureIsEmpty(const SignatureLike& signature) {
    return signature.symbols.empty() && signature.sort_constructors.empty() && signature.symbol_ranges.empty();
}

bool decimalNumeral(const std::string& value) {
    if (value.empty()) { return false; }
    if (value == "0") { return true; }
    if (value.front() < '1' || value.front() > '9') { return false; }
    for (std::size_t i = 1; i < value.size(); ++i) {
        if (value[i] < '0' || value[i] > '9') { return false; }
    }
    return true;
}

bool validIntegerValue(const std::string& value) {
    if (decimalNumeral(value)) { return true; }
    if (value.size() > 1 && value.front() == '-') {
        return decimalNumeral(value.substr(1));
    }
    if (value.size() < 5 || value.compare(0, 3, "(- ") != 0
        || value.back() != ')') {
        return false;
    }
    return decimalNumeral(value.substr(3, value.size() - 4));
}

bool decodeSmtString(const std::string& value, std::string& decoded) {
    if (value.size() < 2 || value.front() != '"' || value.back() != '"') return false;
    for (std::size_t i = 1; i + 1 < value.size(); ++i) {
        if (value[i] != '"') { continue; }
        if (i + 1 >= value.size() - 1 || value[i + 1] != '"') return false;
        ++i;
    }
    // A solver model uses the same Unicode escapes as an SMT String literal.
    // Decode exactly this outer layer; a backslash produced by decoding must
    // not trigger a second pass over the reconstructed source term.
    decoded = ConversionUtils::unescapeString(value.substr(1, value.size() - 2));
    return true;
}

bool isOneSmtTerm(const std::string& text) {
    std::size_t i = 0;
    const auto skipSpace = [&]() {
        while (i < text.size() && std::isspace(static_cast<unsigned char>(text[i]))) ++i;
    };
    skipSpace();
    if (i == text.size()) return false;
    if (text[i] == '(') {
        std::size_t depth = 0;
        bool string = false;
        bool quoted = false;
        for (; i < text.size(); ++i) {
            const char c = text[i];
            if (string) {
                if (c == '"') {
                    if (i + 1 < text.size() && text[i + 1] == '"') ++i;
                    else string = false;
                }
                continue;
            }
            if (quoted) { if (c == '|') quoted = false; continue; }
            if (c == '"') { string = true; continue; }
            if (c == '|') { quoted = true; continue; }
            if (c == '(') ++depth;
            else if (c == ')') {
                if (depth == 0) return false;
                if (--depth == 0) { ++i; break; }
            }
        }
        if (depth != 0 || string || quoted) return false;
    } else if (text[i] == '"') {
        std::size_t end = i + 1;
        bool closed = false;
        for (; end < text.size(); ++end) {
            if (text[end] == '"') {
                if (end + 1 < text.size() && text[end + 1] == '"') { ++end; continue; }
                ++end; closed = true; break;
            }
        }
        if (!closed) return false;
        i = end;
    } else if (text[i] == '|') {
        const std::size_t end = text.find('|', i + 1);
        if (end == std::string::npos) return false;
        i = end + 1;
    } else {
        const std::size_t begin = i;
        while (i < text.size() && !std::isspace(static_cast<unsigned char>(text[i]))
               && text[i] != '(' && text[i] != ')') ++i;
        if (i == begin) return false;
    }
    skipSpace();
    return i == text.size();
}

std::string normalizeIntegerValue(const std::string& value) {
    if (value.size() > 1 && value.front() == '-') {
        const std::string magnitude = value.substr(1);
        return magnitude == "0" ? magnitude : "(- " + magnitude + ")";
    }
    return value;
}

bool decimalToBitVector(const std::string& numeral, unsigned width,
                        std::string& literal) {
    if (width == 0 || !decimalNumeral(numeral)) { return false; }
    std::string value = numeral;
    std::string reversed_bits;
    while (value != "0" && reversed_bits.size() < width) {
        unsigned remainder = 0;
        std::string quotient;
        quotient.reserve(value.size());
        for (char digit : value) {
            const unsigned current = remainder * 10U
                                     + static_cast<unsigned>(digit - '0');
            const unsigned qdigit = current / 2U;
            remainder = current % 2U;
            if (!quotient.empty() || qdigit != 0) {
                quotient.push_back(static_cast<char>('0' + qdigit));
            }
        }
        reversed_bits.push_back(remainder == 0 ? '0' : '1');
        value = quotient.empty() ? "0" : std::move(quotient);
    }
    literal = "#b";
    literal.append(width - reversed_bits.size(), '0');
    literal.append(reversed_bits.rbegin(), reversed_bits.rend());
    return true;
}

bool normalizeBitVectorValue(const std::string& value, unsigned width,
                             std::string& literal) {
    if (width == 0) { return false; }
    if (value.size() >= 2 && value.compare(0, 2, "#b") == 0) {
        if (value.size() - 2 != width
            || !std::all_of(value.begin() + 2, value.end(), [](char c) {
                   return c == '0' || c == '1';
               })) {
            return false;
        }
        literal = value;
        return true;
    }
    if (value.size() >= 2 && value.compare(0, 2, "#x") == 0) {
        const std::size_t digits = value.size() - 2;
        if (width % 4U != 0 || digits != width / 4U
            || !std::all_of(value.begin() + 2, value.end(), [](unsigned char c) {
                   return std::isxdigit(c) != 0;
               })) {
            return false;
        }
        literal = value;
        return true;
    }
    constexpr char prefix[] = "(_ bv";
    if (value.size() <= sizeof(prefix) - 1
        || value.compare(0, sizeof(prefix) - 1, prefix) != 0
        || value.back() != ')') {
        return false;
    }
    const std::size_t width_separator = value.find(' ', sizeof(prefix) - 1);
    if (width_separator == std::string::npos) { return false; }
    const std::string numeral = value.substr(sizeof(prefix) - 1,
                                             width_separator - (sizeof(prefix) - 1));
    std::size_t width_begin = width_separator;
    while (width_begin < value.size() && value[width_begin] == ' ') { ++width_begin; }
    const std::string width_text = value.substr(width_begin,
                                                value.size() - width_begin - 1);
    if (!decimalNumeral(numeral) || !decimalNumeral(width_text)) { return false; }
    unsigned long parsed_width = 0;
    try {
        std::size_t consumed = 0;
        parsed_width = std::stoul(width_text, &consumed);
        if (consumed != width_text.size() || parsed_width != width) { return false; }
    } catch (const std::exception&) {
        return false;
    }
    return decimalToBitVector(numeral, width, literal);
}

std::string canonicalSmtSymbol(const std::string& token) {
    if (token.size() >= 2 && token.front() == '|' && token.back() == '|') {
        return token.substr(1, token.size() - 2);
    }
    return token;
}

bool instantiateChoiceTemplate(
    const std::string& label,
    const std::vector<ChoiceAlternative::Binding>& bindings,
    const Assignment& target, std::string& result, std::string& error) {
    if (bindings.empty()) {
        result = label;
        return true;
    }
    std::map<std::string, const ChoiceAlternative::Binding*> by_placeholder;
    std::set<std::string> target_names;
    for (const ChoiceAlternative::Binding& binding : bindings) {
        const std::string placeholder = canonicalSmtSymbol(binding.placeholder);
        if (binding.placeholder.empty() || binding.target_name.empty()
            || !by_placeholder.emplace(placeholder, &binding).second
            || !target_names.insert(binding.target_name).second) {
            error = "choice template has an empty or duplicate binding";
            return false;
        }
    }

    std::map<std::string, std::size_t> occurrences;
    const auto appendToken = [&](const std::string& token,
                                 const std::string& original) -> bool {
        const auto binding = by_placeholder.find(canonicalSmtSymbol(token));
        if (binding == by_placeholder.end()) {
            result += original;
            return true;
        }
        const auto value = target.find(binding->second->target_name);
        if (value == target.end()) {
            error = "target model has no value for choice binding '"
                  + binding->second->target_name + "'";
            return false;
        }
        const ChoiceAlternative::Binding::Kind kind = binding->second->kind;
        std::string bitvector_literal;
        std::string source_term;
        std::string decoded_string_value;
        const bool valid = kind == ChoiceAlternative::Binding::Kind::INTEGER
                               ? validIntegerValue(value->second)
                           : kind == ChoiceAlternative::Binding::Kind::BOOLEAN
                               ? (value->second == "true" || value->second == "false")
                           : kind == ChoiceAlternative::Binding::Kind::BITVECTOR
                               ? normalizeBitVectorValue(value->second,
                                                          binding->second->bit_width,
                                                          bitvector_literal)
                           : kind == ChoiceAlternative::Binding::Kind::SMT_TERM
                               ? decodeSmtString(value->second, source_term)
                                     && isOneSmtTerm(source_term)
                           : kind == ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE
                               && decodeSmtString(value->second, decoded_string_value)
                               && isOneSmtTerm(value->second);
        if (!valid) {
            error = "target value for choice binding '"
                  + binding->second->target_name + "' has the wrong type";
            return false;
        }
        if (kind == ChoiceAlternative::Binding::Kind::INTEGER) {
            result += normalizeIntegerValue(value->second);
        } else if (kind == ChoiceAlternative::Binding::Kind::BOOLEAN) {
            result += value->second;
        } else if (kind == ChoiceAlternative::Binding::Kind::BITVECTOR) {
            result += bitvector_literal;
        } else if (kind == ChoiceAlternative::Binding::Kind::SMT_TERM) {
            result += source_term;
        } else {
            // Model values are already canonical SMT-LIB String literals; use
            // that token directly as the source expression, preserving every
            // character without invoking the String theory during synthesis.
            result += value->second;
        }
        ++occurrences[binding->first];
        return true;
    };

    result.clear();
    for (std::size_t i = 0; i < label.size();) {
        if (label[i] == ';') {
            const std::size_t end = label.find('\n', i);
            const std::size_t length = end == std::string::npos
                                           ? label.size() - i
                                           : end - i;
            result.append(label, i, length);
            i += length;
            continue;
        }
        if (label[i] == '"') {
            const std::size_t begin = i++;
            while (i < label.size()) {
                if (label[i++] == '"') {
                    if (i < label.size() && label[i] == '"') { ++i; }
                    else { break; }
                }
            }
            result.append(label, begin, i - begin);
            continue;
        }
        if (label[i] == '|') {
            const std::size_t begin = i++;
            while (i < label.size() && label[i] != '|') { ++i; }
            if (i < label.size()) { ++i; }
            const std::string original = label.substr(begin, i - begin);
            if (!appendToken(original, original)) { return false; }
            continue;
        }
        if (std::isspace(static_cast<unsigned char>(label[i]))
            || label[i] == '(' || label[i] == ')') {
            result.push_back(label[i++]);
            continue;
        }

        const std::size_t begin = i;
        while (i < label.size()
               && !std::isspace(static_cast<unsigned char>(label[i]))
               && label[i] != '(' && label[i] != ')' && label[i] != ';') {
            ++i;
        }
        const std::string token = label.substr(begin, i - begin);
        if (!appendToken(token, token)) { return false; }
    }
    for (const auto& binding : by_placeholder) {
        if (occurrences[binding.first] == 0) {
            error = "choice template is missing placeholder '" + binding.first + "'";
            return false;
        }
    }
    return true;
}

} // namespace

AssumptionProfile AssumptionProfile::miniZinc() {
    AssumptionProfile p;
    p.id = "minizinc-2.10";
    p.carriers = CarrierSemantics::MIXED;
    p.carrier_emptiness = CarrierEmptiness::MIXED;
    p.functions = FunctionSemantics::PARTIAL;
    p.undefined = UndefinedSemantics::RELATIONAL_FALSE;
    p.arithmetic = ArithmeticSemantics::MIXED;
    p.overflow = OverflowSemantics::ABORT;
    p.division = DivisionSemantics::TRUNCATE_TOWARD_ZERO;
    p.arrays = ArraySemantics::FINITE_PARTIAL;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::FINITE_EXPANSION;
    p.invalid_phase = PhaseSemantics::MIXED;
    p.annotations = AnnotationSemantics::STRATEGY_ONLY;
    return p;
}

AssumptionProfile AssumptionProfile::flatZinc() {
    AssumptionProfile p;
    p.id = "flatzinc-1.6";
    p.carriers = CarrierSemantics::MIXED;
    p.carrier_emptiness = CarrierEmptiness::MIXED;
    p.functions = FunctionSemantics::PARTIAL;
    p.undefined = UndefinedSemantics::RELATIONAL_FALSE;
    p.arithmetic = ArithmeticSemantics::MIXED;
    p.overflow = OverflowSemantics::ABORT;
    p.division = DivisionSemantics::TRUNCATE_TOWARD_ZERO;
    p.arrays = ArraySemantics::FINITE_PARTIAL;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::NONE;
    p.invalid_phase = PhaseSemantics::MIXED;
    p.annotations = AnnotationSemantics::MIXED;
    return p;
}

AssumptionProfile AssumptionProfile::essencePrime() {
    AssumptionProfile p;
    p.id = "essence-prime-1.0";
    p.carriers = CarrierSemantics::FINITE;
    p.carrier_emptiness = CarrierEmptiness::MIXED;
    p.functions = FunctionSemantics::PARTIAL;
    p.undefined = UndefinedSemantics::RELATIONAL_FALSE;
    p.arithmetic = ArithmeticSemantics::INTEGER;
    p.overflow = OverflowSemantics::ABORT;
    p.division = DivisionSemantics::FLOOR;
    p.arrays = ArraySemantics::FINITE_PARTIAL;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::FINITE_EXPANSION;
    p.invalid_phase = PhaseSemantics::MIXED;
    p.annotations = AnnotationSemantics::STRATEGY_ONLY;
    return p;
}

AssumptionProfile AssumptionProfile::xcsp3() {
    AssumptionProfile p;
    p.id = "xcsp3-core-3.2";
    p.carriers = CarrierSemantics::FINITE;
    p.carrier_emptiness = CarrierEmptiness::NONEMPTY;
    p.functions = FunctionSemantics::PARTIAL;
    p.undefined = UndefinedSemantics::RELATIONAL_FALSE;
    p.arithmetic = ArithmeticSemantics::INTEGER;
    p.overflow = OverflowSemantics::ABORT;
    p.division = DivisionSemantics::TRUNCATE_TOWARD_ZERO;
    p.arrays = ArraySemantics::FIXED_VECTOR;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::NONE;
    p.invalid_phase = PhaseSemantics::CONSTRAINT_FAILURE;
    p.annotations = AnnotationSemantics::STRATEGY_ONLY;
    return p;
}

AssumptionProfile AssumptionProfile::typedRelationalCore() {
    AssumptionProfile p;
    p.id = "typed-relational-optimization-core-v1";
    p.carriers = CarrierSemantics::MIXED;
    p.carrier_emptiness = CarrierEmptiness::MIXED;
    p.functions = FunctionSemantics::PARTIAL;
    p.undefined = UndefinedSemantics::RELATIONAL_FALSE;
    p.arithmetic = ArithmeticSemantics::MIXED;
    p.overflow = OverflowSemantics::UNBOUNDED;
    p.division = DivisionSemantics::MIXED;
    p.arrays = ArraySemantics::FINITE_PARTIAL;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::MIXED;
    p.invalid_phase = PhaseSemantics::MIXED;
    p.annotations = AnnotationSemantics::STRATEGY_ONLY;
    return p;
}

AssumptionProfile AssumptionProfile::smtLib() {
    AssumptionProfile p;
    p.id = "smt-lib-2.7";
    p.carriers = CarrierSemantics::MIXED;
    p.carrier_emptiness = CarrierEmptiness::NONEMPTY;
    p.functions = FunctionSemantics::TOTAL;
    p.undefined = UndefinedSemantics::TARGET_DEFINED;
    p.arithmetic = ArithmeticSemantics::MIXED;
    p.overflow = OverflowSemantics::UNBOUNDED;
    p.division = DivisionSemantics::EUCLIDEAN;
    p.arrays = ArraySemantics::TOTAL_EXTENSIONAL;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::NATIVE;
    p.invalid_phase = PhaseSemantics::UNDEFINED_VALUE;
    p.annotations = AnnotationSemantics::NONE;
    return p;
}

AssumptionProfile AssumptionProfile::omt() {
    AssumptionProfile p = smtLib();
    p.id = "omt-over-smt-lib-v1";
    return p;
}

std::string SymbolPatternRange::name(std::uint64_t offset) const {
    if (offset>=count || offset>std::numeric_limits<std::uint64_t>::max()-first)
        throw std::out_of_range("SymbolPatternRange::name offset is outside range");
    return prefix+std::to_string(first+offset)+suffix;
}

Sentence DeclarationBoundsAxiom::materialize(const SignatureSnapshot& signature) const {
    if (!validDeclarationBounds(*this, signature)) { return {}; }
    const auto& symbol = signature.symbols[target_symbol_index];
    const auto variable = H::mkIdent(symbol.name, symbol.codomain);
    if (lower_bound && upper_bound) {
        return H::mkOp(H::Op::LE, {lower_bound, variable, upper_bound}, loc);
    }
    return lower_bound
        ? H::mkOp(H::Op::GE, {variable, lower_bound}, loc)
        : H::mkOp(H::Op::LE, {variable, upper_bound}, loc);
}

Signature signatureOf(const H::ConstraintModel& model) {
    Signature result;
    result.sort_constructors.reserve(model.uninterpreted_sorts.size());
    for (const H::UninterpretedSortDecl& sort : model.uninterpreted_sorts) {
        result.sort_constructors.push_back({sort.name, sort.arity});
    }
    result.symbols.reserve(model.decls.size() + model.funs.size());
    for (const H::VarDecl& declaration : model.decls) {
        result.symbols.push_back(
            Symbol{declaration.name, SymbolKind::CONSTANT, {}, declaration.sort});
    }
    for (const H::BoolVarRange& range : model.bool_var_ranges) {
        result.symbol_ranges.push_back(
            SymbolPatternRange{range.prefix,range.first,range.count,SymbolKind::CONSTANT,{},range.sort});
    }
    for (const H::ScalarVarRange& range : model.scalar_var_ranges) {
        result.symbol_ranges.push_back(
            {range.prefix, range.first, range.count, SymbolKind::CONSTANT,
             {}, range.sort, range.suffix});
    }
    for (const H::FunDecl& declaration : model.funs) {
        result.symbols.push_back(Symbol{declaration.name,
                                        declaration.result.kind == H::SortKind::BOOL
                                            ? SymbolKind::RELATION
                                            : SymbolKind::FUNCTION,
                                        declaration.params,
                                        declaration.result});
    }
    for (const H::DatatypeDecl& declaration : model.datatypes) {
        const H::Sort datatype = H::Sort::datatype(declaration.name);
        result.symbols.push_back(
            Symbol{declaration.name, SymbolKind::SORT, {}, datatype});
        for (const H::DtConstructor& constructor : declaration.constructors) {
            std::vector<H::Sort> fields;
            fields.reserve(constructor.selectors.size());
            for (const H::DtSelector& selector : constructor.selectors) {
                fields.push_back(selector.sort);
                result.symbols.push_back(
                    Symbol{selector.name, SymbolKind::FUNCTION, {datatype},
                           selector.sort});
            }
            result.symbols.push_back(
                Symbol{constructor.name, SymbolKind::FUNCTION, std::move(fields), datatype});
            result.symbols.push_back(
                Symbol{"is-" + constructor.name, SymbolKind::RELATION, {datatype},
                       H::Sort::boolean()});
        }
    }
    return result;
}

SignatureSnapshot::SignatureSnapshot(Signature value)
    : owner_(std::make_shared<const Signature>(std::move(value))),
      symbols(owner_, &owner_->symbols),
      symbol_ranges(owner_, &owner_->symbol_ranges),
      sort_constructors(owner_, &owner_->sort_constructors) {}

std::uint64_t SignatureSnapshot::symbolCount() const noexcept {
    std::uint64_t count=static_cast<std::uint64_t>(symbols.size());
    for (const SymbolPatternRange& range:symbol_ranges) {
        if (range.count>std::numeric_limits<std::uint64_t>::max()-count)
            return std::numeric_limits<std::uint64_t>::max();
        count+=range.count;
    }
    return count;
}

SignatureSnapshot& SignatureSnapshot::operator=(const SignatureSnapshot& other) {
    if (this != &other) {
        owner_ = other.owner_;
        symbols = other.symbols;
        symbol_ranges = other.symbol_ranges;
        sort_constructors = other.sort_constructors;
    }
    return *this;
}

SignatureSnapshot& SignatureSnapshot::operator=(SignatureSnapshot&& other) noexcept {
    if (this != &other) {
        owner_ = std::move(other.owner_);
        symbols = std::move(other.symbols);
        symbol_ranges = std::move(other.symbol_ranges);
        sort_constructors = std::move(other.sort_constructors);
    }
    return *this;
}

Signature SignatureSnapshot::materialize() const {
    Signature value;
    value.symbols.assign(symbols.begin(), symbols.end());
    value.sort_constructors.assign(sort_constructors.begin(), sort_constructors.end());
    value.symbol_ranges.assign(symbol_ranges.begin(), symbol_ranges.end());
    return value;
}

SignatureSnapshot SignatureSnapshot::symbolPrefix(std::size_t count) const {
    if (count > symbols.size()) {
        throw std::out_of_range("signature symbol prefix exceeds its source view");
    }
    SignatureSnapshot result = *this;
    if (owner_) {
        result.symbols = ReadOnlySignatureVector<Symbol>(owner_, &owner_->symbols, count);
    }
    return result;
}

bool signatureMatchesModel(const SignatureSnapshot& signature,
                           const H::ConstraintModel& model) {
    if (signature.sort_constructors.size() != model.uninterpreted_sorts.size()) {
        return false;
    }
    for (std::size_t i = 0; i < model.uninterpreted_sorts.size(); ++i) {
        const auto& expected = signature.sort_constructors[i];
        const auto& actual = model.uninterpreted_sorts[i];
        if (expected.name != actual.name || expected.arity != actual.arity) {
            return false;
        }
    }

    std::size_t symbol_index = 0;
    const auto matches = [&](const std::string& name, SymbolKind kind,
                             const std::vector<H::Sort>& domain,
                             const H::Sort& codomain) {
        if (symbol_index >= signature.symbols.size()) { return false; }
        const Symbol& actual = signature.symbols[symbol_index++];
        if (actual.name != name || actual.kind != kind
            || actual.domain.size() != domain.size()
            || !H::sameSort(actual.codomain, codomain)) {
            return false;
        }
        for (std::size_t i = 0; i < domain.size(); ++i) {
            if (!H::sameSort(actual.domain[i], domain[i])) { return false; }
        }
        return true;
    };
    const auto isDatatype = [](const H::Sort& sort, const std::string& name) {
        return sort.kind == H::SortKind::DATATYPE && sort.name == name
            && sort.args.empty();
    };
    const auto matchesDatatypeSymbol = [&](const std::string& name,
                                           SymbolKind kind,
                                           const std::string& datatype_name,
                                           const H::Sort* selector_sort,
                                           const H::DtConstructor* constructor,
                                           bool recognizer) {
        if (symbol_index >= signature.symbols.size()) { return false; }
        const Symbol& actual = signature.symbols[symbol_index++];
        const bool name_matches = recognizer
            ? actual.name.size() == name.size() + 3
                && actual.name.compare(0, 3, "is-") == 0
                && actual.name.compare(3, name.size(), name) == 0
            : actual.name == name;
        if (!name_matches || actual.kind != kind) { return false; }
        if (selector_sort) {
            return actual.domain.size() == 1
                && isDatatype(actual.domain.front(), datatype_name)
                && H::sameSort(actual.codomain, *selector_sort);
        }
        if (recognizer) {
            return actual.domain.size() == 1
                && isDatatype(actual.domain.front(), datatype_name)
                && actual.codomain.kind == H::SortKind::BOOL;
        }
        if (constructor) {
            if (actual.domain.size() != constructor->selectors.size()
                || !isDatatype(actual.codomain, datatype_name)) {
                return false;
            }
            for (std::size_t i = 0; i < constructor->selectors.size(); ++i) {
                if (!H::sameSort(actual.domain[i],
                                 constructor->selectors[i].sort)) {
                    return false;
                }
            }
            return true;
        }
        return actual.domain.empty() && isDatatype(actual.codomain, datatype_name);
    };
    const std::vector<H::Sort> no_domain;
    for (const H::VarDecl& declaration : model.decls) {
        if (!matches(declaration.name, SymbolKind::CONSTANT, no_domain,
                     declaration.sort)) {
            return false;
        }
    }
    if (signature.symbol_ranges.size()
        != model.bool_var_ranges.size() + model.scalar_var_ranges.size()) return false;
    for (std::size_t i=0;i<model.bool_var_ranges.size();++i) {
        const H::BoolVarRange& expected=model.bool_var_ranges[i];
        const SymbolPatternRange& actual=signature.symbol_ranges[i];
        if (actual.prefix!=expected.prefix||!actual.suffix.empty()||actual.first!=expected.first
            ||actual.count!=expected.count||actual.kind!=SymbolKind::CONSTANT
            ||!actual.domain.empty()||!H::sameSort(actual.codomain,expected.sort)) return false;
    }
    for (std::size_t i = 0; i < model.scalar_var_ranges.size(); ++i) {
        const auto& expected = model.scalar_var_ranges[i];
        const auto& actual = signature.symbol_ranges[model.bool_var_ranges.size() + i];
        if (actual.prefix != expected.prefix || actual.suffix != expected.suffix
            || actual.first != expected.first || actual.count != expected.count
            || actual.kind != SymbolKind::CONSTANT || !actual.domain.empty()
            || !H::sameSort(actual.codomain, expected.sort)) return false;
    }
    for (const H::FunDecl& declaration : model.funs) {
        const SymbolKind kind = declaration.result.kind == H::SortKind::BOOL
            ? SymbolKind::RELATION : SymbolKind::FUNCTION;
        if (!matches(declaration.name, kind, declaration.params,
                     declaration.result)) {
            return false;
        }
    }
    for (const H::DatatypeDecl& declaration : model.datatypes) {
        if (!matchesDatatypeSymbol(declaration.name, SymbolKind::SORT,
                                   declaration.name, nullptr, nullptr, false)) {
            return false;
        }
        for (const H::DtConstructor& constructor : declaration.constructors) {
            for (const H::DtSelector& selector : constructor.selectors) {
                if (!matchesDatatypeSymbol(selector.name, SymbolKind::FUNCTION,
                                           declaration.name, &selector.sort,
                                           nullptr, false)) {
                    return false;
                }
            }
            if (!matchesDatatypeSymbol(constructor.name, SymbolKind::FUNCTION,
                                       declaration.name, nullptr, &constructor,
                                       false)
                || !matchesDatatypeSymbol(constructor.name,
                                          SymbolKind::RELATION,
                                          declaration.name, nullptr, nullptr,
                                          true)) {
                return false;
            }
        }
    }
    return symbol_index == signature.symbols.size();
}

bool ModelProjection::project(const Assignment& target, Assignment& source,
                              Diagnostics& diags) const {
    source.clear();
    std::set<std::string> seen;
    for (const Observable& observable : observables) {
        if (observable.source_name.empty() || observable.target_name.empty()) {
            diags.error(ErrorCode::E_INTERNAL,
                        "model projection contains an empty source or target name");
            return false;
        }
        if (!seen.insert(observable.source_name).second) {
            diags.error(ErrorCode::E_INTERNAL,
                        "model projection defines source observable '"
                            + observable.source_name + "' more than once");
            return false;
        }
        std::string value;
        if (observable.projection == ProjectionKind::CONSTANT) {
            value = observable.target_name;
        } else {
            const auto it = target.find(observable.target_name);
            if (it == target.end()) {
                diags.error(ErrorCode::E_INTERNAL,
                            "target model has no value for observable '"
                                + observable.target_name + "'");
                return false;
            }
            value = it->second;
        }
        if (observable.projection == ProjectionKind::BOOL_FROM_ZERO_ONE) {
            if (value == "0") { value = "false"; }
            else if (value == "1") { value = "true"; }
            else {
                diags.error(ErrorCode::E_INTERNAL,
                            "observable '" + observable.target_name
                                + "' is neither 0 nor 1 and cannot decode as Bool");
                return false;
            }
        }
        source.emplace(observable.source_name, std::move(value));
    }
    for (const Observable& observable : optional_observables) {
        if (observable.source_name.empty() || observable.target_name.empty()
            || observable.projection != ProjectionKind::DIRECT) {
            diags.error(ErrorCode::E_INTERNAL,
                        "optional projection contains an empty name or non-direct mapping");
            return false;
        }
        if (!seen.insert(observable.source_name).second) {
            diags.error(ErrorCode::E_INTERNAL,
                        "model projection defines source observable '"
                            + observable.source_name + "' more than once");
            return false;
        }
        const auto value = target.find(observable.target_name);
        if (value != target.end()) { source.emplace(observable.source_name, value->second); }
    }
    for (const ObservableRange& range : observable_ranges) {
        if (range.source_prefix.empty() || range.target_prefix.empty() || range.count == 0
            || range.source_first > std::numeric_limits<std::uint64_t>::max() - (range.count - 1)
            || range.target_first > std::numeric_limits<std::uint64_t>::max() - (range.count - 1)) {
            diags.error(ErrorCode::E_INTERNAL, "model projection contains an invalid observable range");
            return false;
        }
        for (std::uint64_t offset = 0; offset < range.count; ++offset) {
            const std::string source_name = range.source_prefix + std::to_string(range.source_first + offset) + range.source_suffix;
            const std::string target_name = range.target_prefix + std::to_string(range.target_first + offset) + range.target_suffix;
            if (!seen.insert(source_name).second) {
                diags.error(ErrorCode::E_INTERNAL, "model projection defines source observable '" + source_name + "' more than once");
                return false;
            }
            const auto it = target.find(target_name);
            if (it == target.end()) {
                diags.error(ErrorCode::E_INTERNAL, "target model has no value for observable '" + target_name + "'");
                return false;
            }
            std::string value = it->second;
            if (range.projection == ProjectionKind::BOOL_FROM_ZERO_ONE) {
                if (value == "0") value = "false";
                else if (value == "1") value = "true";
                else { diags.error(ErrorCode::E_INTERNAL, "range observable '" + target_name + "' is neither 0 nor 1"); return false; }
            } else if (range.projection == ProjectionKind::CONSTANT) {
                diags.error(ErrorCode::E_INTERNAL, "constant projection is not supported for a variable range");
                return false;
            }
            source.emplace(source_name, std::move(value));
        }
    }
    for (const ChoiceObservable& choice : choices) {
        if (choice.source_name.empty() || choice.alternatives.empty()) {
            diags.error(ErrorCode::E_INTERNAL,
                        "choice projection contains an empty source name or no alternatives");
            return false;
        }
        if (!seen.insert(choice.source_name).second) {
            diags.error(ErrorCode::E_INTERNAL,
                        "model projection defines source observable '"
                            + choice.source_name + "' more than once");
            return false;
        }
        const ChoiceAlternative* selected = nullptr;
        std::set<std::string> target_names;
        bool saw_omitted_alternative = choice.omit_label.empty();
        for (const ChoiceAlternative& alternative : choice.alternatives) {
            if (alternative.label.empty() || alternative.target_name.empty()
                || !target_names.insert(alternative.target_name).second) {
                diags.error(ErrorCode::E_INTERNAL,
                            "choice projection for '" + choice.source_name
                                + "' contains an empty or duplicate alternative");
                return false;
            }
            if (alternative.label == choice.omit_label) {
                saw_omitted_alternative = true;
            }
            std::set<std::string> binding_placeholders;
            std::set<std::string> binding_targets;
            for (const ChoiceAlternative::Binding& binding : alternative.bindings) {
                if (binding.placeholder.empty() || binding.target_name.empty()
                    || !binding_placeholders.insert(binding.placeholder).second
                    || !binding_targets.insert(binding.target_name).second
                    || binding.target_name == alternative.target_name) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "choice projection for '" + choice.source_name
                                    + "' has an empty or duplicate binding");
                    return false;
                }
                if (binding.kind != ChoiceAlternative::Binding::Kind::INTEGER
                    && binding.kind != ChoiceAlternative::Binding::Kind::BOOLEAN
                    && binding.kind != ChoiceAlternative::Binding::Kind::BITVECTOR
                    && binding.kind != ChoiceAlternative::Binding::Kind::SMT_TERM
                    && binding.kind != ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "choice projection for '" + choice.source_name
                                    + "' has an unknown binding type");
                    return false;
                }
                if ((binding.kind == ChoiceAlternative::Binding::Kind::BITVECTOR
                     && binding.bit_width == 0)
                    || (binding.kind != ChoiceAlternative::Binding::Kind::BITVECTOR
                        && binding.bit_width != 0)) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "choice projection for '" + choice.source_name
                                    + "' has an invalid bit-vector binding width");
                    return false;
                }
            }
            const auto it = target.find(alternative.target_name);
            if (it == target.end()) {
                diags.error(ErrorCode::E_INTERNAL,
                            "target model has no value for choice alternative '"
                                + alternative.target_name + "'");
                return false;
            }
            const bool is_true = it->second == "true" || it->second == "1";
            const bool is_false = it->second == "false" || it->second == "0";
            if (!is_true && !is_false) {
                diags.error(ErrorCode::E_INTERNAL,
                            "choice alternative '" + alternative.target_name
                                + "' is not Boolean");
                return false;
            }
            if (!is_true) { continue; }
            if (selected != nullptr) {
                diags.error(ErrorCode::E_INTERNAL,
                            "choice projection for '" + choice.source_name
                                + "' has more than one selected alternative");
                return false;
            }
            selected = &alternative;
        }
        if (selected == nullptr) {
            diags.error(ErrorCode::E_INTERNAL,
                        "choice projection for '" + choice.source_name
                            + "' has no selected alternative");
            return false;
        }
        if (!saw_omitted_alternative) {
            diags.error(ErrorCode::E_INTERNAL,
                        "choice projection for '" + choice.source_name
                            + "' names an omit label that is not an alternative");
            return false;
        }
        if (selected->label != choice.omit_label) {
            std::string projected_label;
            std::string error;
            if (!instantiateChoiceTemplate(selected->label, selected->bindings,
                                           target, projected_label, error)) {
                diags.error(ErrorCode::E_INTERNAL,
                            "choice projection for '" + choice.source_name
                                + "' failed: " + error);
                return false;
            }
            source.emplace(choice.source_name, std::move(projected_label));
        }
    }
    for (const GrammarChoiceObservable& grammar : grammar_choices) {
        if (grammar.source_name.empty() || grammar.nodes.empty()
            || grammar.root_node >= grammar.nodes.size()) {
            diags.error(ErrorCode::E_INTERNAL,
                        "grammar projection contains an empty source name or invalid root");
            return false;
        }
        if (!seen.insert(grammar.source_name).second) {
            diags.error(ErrorCode::E_INTERNAL,
                        "model projection defines source observable '"
                            + grammar.source_name + "' more than once");
            return false;
        }

        std::set<std::string> selector_names;
        for (const GrammarChoiceNode& node : grammar.nodes) {
            if (node.alternatives.empty()
                || (node.selector_target.empty() && node.alternatives.size() != 1)
                || (!node.selector_target.empty()
                    && !selector_names.insert(node.selector_target).second)) {
                diags.error(ErrorCode::E_INTERNAL,
                            "grammar projection contains an empty/duplicate selector or no production");
                return false;
            }
            for (const GrammarChoiceAlternative& alternative : node.alternatives) {
                if (alternative.label.empty()
                    || alternative.children.size() != alternative.child_placeholders.size()) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "grammar projection contains a malformed production template");
                    return false;
                }
                std::set<std::string> child_names;
                for (std::size_t i = 0; i < alternative.children.size(); ++i) {
                    if (alternative.children[i] >= grammar.nodes.size()
                        || alternative.child_placeholders[i].empty()
                        || !child_names.insert(canonicalSmtSymbol(
                               alternative.child_placeholders[i])).second) {
                        diags.error(ErrorCode::E_INTERNAL,
                                    "grammar production has an invalid or duplicate child reference");
                        return false;
                    }
                }
                std::set<std::string> binding_names;
                std::set<std::string> binding_targets;
                for (const ChoiceAlternative::Binding& binding : alternative.bindings) {
                    if (binding.placeholder.empty() || binding.target_name.empty()
                        || !binding_names.insert(canonicalSmtSymbol(binding.placeholder)).second
                        || !binding_targets.insert(binding.target_name).second
                        || binding.kind < ChoiceAlternative::Binding::Kind::INTEGER
                        || binding.kind > ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE
                        || (binding.kind == ChoiceAlternative::Binding::Kind::BITVECTOR
                            ? binding.bit_width == 0 : binding.bit_width != 0)) {
                        diags.error(ErrorCode::E_INTERNAL,
                                    "grammar production has an invalid or duplicate typed binding");
                        return false;
                    }
                }
                for (const std::string& child_name : child_names) {
                    if (binding_names.count(child_name) != 0) {
                        diags.error(ErrorCode::E_INTERNAL,
                                    "grammar production reuses a token as both a child and binding placeholder");
                        return false;
                    }
                }
            }
        }

        // Validate the entire projection graph, including currently inactive
        // branches. The assignment is consulted only for nodes reachable from
        // the selected root production below.
        // Validate the complete graph iteratively. A legal bounded grammar
        // can have a long unary production chain; recursive DFS makes the
        // projection path depend on the C++ call-stack limit.
        std::vector<unsigned char> marks(grammar.nodes.size(), 0);
        struct DfsFrame {
            std::size_t node;
            std::size_t alternative = 0;
            std::size_t child = 0;
        };
        std::vector<DfsFrame> dfs;
        for (std::size_t start = 0; start < grammar.nodes.size(); ++start) {
            if (marks[start] == 2) { continue; }
            marks[start] = 1;
            dfs.push_back({start, 0, 0});
            while (!dfs.empty()) {
                DfsFrame& frame = dfs.back();
                const auto& alternatives = grammar.nodes[frame.node].alternatives;
                if (frame.alternative == alternatives.size()) {
                    marks[frame.node] = 2;
                    dfs.pop_back();
                    continue;
                }
                const auto& children = alternatives[frame.alternative].children;
                if (frame.child == children.size()) {
                    ++frame.alternative;
                    frame.child = 0;
                    continue;
                }
                const std::size_t child = children[frame.child++];
                if (marks[child] == 1) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "grammar projection contains a cycle");
                    return false;
                }
                if (marks[child] == 0) {
                    marks[child] = 1;
                    dfs.push_back({child, 0, 0});
                }
            }
        }

        // Expand only the selected derivation with an explicit work stack.
        // This avoids caching complete subtree strings (quadratic for unary
        // chains) and keeps bindings scoped to the template where they occur.
        struct RenderTask {
            bool expand_node = false;
            std::size_t node = 0;
            std::string text;
        };
        std::vector<RenderTask> tasks{{true, grammar.root_node, {}}};
        std::string body;
        while (!tasks.empty()) {
            RenderTask task = std::move(tasks.back());
            tasks.pop_back();
            if (!task.expand_node) {
                body += task.text;
                continue;
            }
            const GrammarChoiceNode& node = grammar.nodes[task.node];
            std::size_t selected_index = 0;
            if (!node.selector_target.empty()) {
                const auto selector = target.find(node.selector_target);
                if (selector == target.end() || !decimalNumeral(selector->second)) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "target model has no nonnegative integer grammar selector '"
                                    + node.selector_target + "'");
                    return false;
                }
                try {
                    std::size_t consumed = 0;
                    const unsigned long long parsed =
                        std::stoull(selector->second, &consumed);
                    if (consumed != selector->second.size()
                        || parsed >= node.alternatives.size()) {
                        diags.error(ErrorCode::E_INTERNAL,
                                    "grammar selector '" + node.selector_target
                                        + "' is outside its production range");
                        return false;
                    }
                    selected_index = static_cast<std::size_t>(parsed);
                } catch (const std::exception&) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "grammar selector '" + node.selector_target
                                    + "' is not a representable nonnegative integer");
                    return false;
                }
            }

            const GrammarChoiceAlternative& alternative =
                node.alternatives[selected_index];
            std::string instantiated;
            std::string error;
            if (!instantiateChoiceTemplate(alternative.label, alternative.bindings,
                                           target, instantiated, error)) {
                diags.error(ErrorCode::E_INTERNAL,
                            "grammar projection for '" + grammar.source_name
                                + "' failed: " + error);
                return false;
            }
            std::map<std::string, std::size_t> child_nodes;
            for (std::size_t i = 0; i < alternative.children.size(); ++i) {
                child_nodes.emplace(canonicalSmtSymbol(
                                        alternative.child_placeholders[i]),
                                    alternative.children[i]);
            }
            std::map<std::string, std::size_t> occurrences;
            std::vector<RenderTask> pieces;
            const auto appendAtom = [&](const std::string& token,
                                        const std::string& original) {
                const std::string canonical = canonicalSmtSymbol(token);
                const auto child = child_nodes.find(canonical);
                if (child == child_nodes.end()) {
                    pieces.push_back({false, 0, original});
                } else {
                    ++occurrences[canonical];
                    pieces.push_back({true, child->second, {}});
                }
            };
            for (std::size_t i = 0; i < instantiated.size();) {
                if (instantiated[i] == ';') {
                    const std::size_t end = instantiated.find('\n', i);
                    const std::size_t length = end == std::string::npos
                        ? instantiated.size() - i : end - i;
                    pieces.push_back({false, 0, instantiated.substr(i, length)});
                    i += length;
                    continue;
                }
                if (instantiated[i] == '"') {
                    const std::size_t begin = i++;
                    while (i < instantiated.size()) {
                        if (instantiated[i++] == '"') {
                            if (i < instantiated.size() && instantiated[i] == '"') {
                                ++i;
                            } else { break; }
                        }
                    }
                    pieces.push_back({false, 0,
                                      instantiated.substr(begin, i - begin)});
                    continue;
                }
                if (instantiated[i] == '|') {
                    const std::size_t begin = i++;
                    while (i < instantiated.size() && instantiated[i] != '|') { ++i; }
                    if (i < instantiated.size()) { ++i; }
                    const std::string token = instantiated.substr(begin, i - begin);
                    appendAtom(token, token);
                    continue;
                }
                if (std::isspace(static_cast<unsigned char>(instantiated[i]))
                    || instantiated[i] == '(' || instantiated[i] == ')') {
                    pieces.push_back({false, 0, instantiated.substr(i, 1)});
                    ++i;
                    continue;
                }
                const std::size_t begin = i;
                while (i < instantiated.size()
                       && !std::isspace(static_cast<unsigned char>(instantiated[i]))
                       && instantiated[i] != '(' && instantiated[i] != ')'
                       && instantiated[i] != ';') { ++i; }
                const std::string token = instantiated.substr(begin, i - begin);
                appendAtom(token, token);
            }
            for (const auto& child : child_nodes) {
                if (occurrences[child.first] == 0) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "grammar projection for '" + grammar.source_name
                                    + "' failed: production is missing child placeholder '"
                                    + child.first + "'");
                    return false;
                }
            }
            for (auto piece = pieces.rbegin(); piece != pieces.rend(); ++piece) {
                tasks.push_back(std::move(*piece));
            }
        }
        source.emplace(grammar.source_name,
                       grammar.prefix + body + grammar.suffix);
    }
    return true;
}

ObjectiveOrder objectiveOrderOf(const H::ConstraintModel& model) {
    const std::size_t soft_count = H::softObjectiveGroups(model).size();
    const std::size_t count = soft_count + model.objectives.size();
    if (count == 0) return ObjectiveOrder::SATISFACTION;
    if (count == 1) {
        return soft_count != 0 || model.objectives.front().kind == H::ObjKind::MINIMIZE
            ? ObjectiveOrder::MINIMIZE : ObjectiveOrder::MAXIMIZE;
    }
    switch (model.objective_combination) {
    case H::ObjectiveCombination::SINGLE:
    case H::ObjectiveCombination::LEXICOGRAPHIC: return ObjectiveOrder::LEXICOGRAPHIC;
    case H::ObjectiveCombination::PARETO:        return ObjectiveOrder::PARETO;
    case H::ObjectiveCombination::BOX:           return ObjectiveOrder::BOX;
    case H::ObjectiveCombination::MINMAX:        return ObjectiveOrder::MINMAX;
    case H::ObjectiveCombination::MAXMIN:        return ObjectiveOrder::MAXMIN;
    }
    return ObjectiveOrder::SATISFACTION;
}

bool hasOptimization(const H::ConstraintModel& model) {
    return objectiveOrderOf(model) != ObjectiveOrder::SATISFACTION;
}

bool TranslationContract::validate(Diagnostics& diags) const {
    if (id.empty() || sentence_translation_id.empty()
        || source.id.empty() || target.id.empty()) {
        diags.error(ErrorCode::E_INTERNAL,
                    "a semantic translation contract needs non-empty stage, alpha, source, "
                    "and target ids");
        return false;
    }
    bool ok = true;
    if (source.assumptions.id.empty() || target.assumptions.id.empty()
        || source.sentence_space.empty() || target.sentence_space.empty()
        || source.model_class.empty() || target.model_class.empty()
        || source.satisfaction_relation.empty()
        || target.satisfaction_relation.empty()) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' does not define Sen, Mod, satisfaction, and assumption "
                          "profiles for both institutions");
        ok = false;
    }
    for (std::size_t i = 0; i < sort_map.size(); ++i) {
        for (std::size_t j = i + 1; j < sort_map.size(); ++j) {
            if (H::sameSort(sort_map[i].source, sort_map[j].source)) {
                diags.error(ErrorCode::E_INTERNAL,
                            "semantic contract '" + id
                                + "' maps source sort '"
                                + H::toString(sort_map[i].source) + "' more than once");
                ok = false;
            }
        }
    }

    std::unordered_set<std::string_view> mapped;
    mapped.reserve(symbol_map.size());
    // Indexed once, not scanned per mapping -- see indexSymbols.
    const SymbolIndex source_index = indexSymbols(source_signature);
    SymbolIndex target_index_storage;
    const bool same_signature_storage =
        source_signature.sharesStorageWith(target_signature);
    if (!same_signature_storage) {
        target_index_storage = indexSymbols(target_signature);
    }
    const SymbolIndex& target_index = same_signature_storage
        ? source_index : target_index_storage;
    for (const SymbolMapping& mapping : symbol_map) {
        if (mapping.source.empty() || mapping.target.empty()
            || !mapped.insert(mapping.source).second) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + id
                            + "' contains an empty or duplicate source symbol mapping");
            ok = false;
            continue;
        }
        const SymbolRange source_symbols = lookup(source_index, mapping.source);
        const SymbolRange target_symbols = lookup(target_index, mapping.target);
        if (source_symbols.empty() || target_symbols.empty()) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + id + "' maps unknown symbol '"
                            + mapping.source + "' to '" + mapping.target + "'");
            ok = false;
        } else if (!namedSymbolsMap(*this, source_symbols, target_symbols)) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + id
                            + "' has an ambiguous or ill-sorted mapping from '"
                            + mapping.source + "' to '" + mapping.target + "'");
            ok = false;
        }
    }
    struct CoveredSymbolRange { std::string prefix; std::string suffix; std::uint64_t first; std::uint64_t last; };
    std::vector<CoveredSymbolRange> covered_ranges;
    for (const SymbolRangeMapping& mapping : symbol_range_map) {
        const auto find_range = [](const SignatureSnapshot& signature, const std::string& prefix,
                                   const std::string& suffix, std::uint64_t first, std::uint64_t count) -> const SymbolPatternRange* {
            for (const SymbolPatternRange& range : signature.symbol_ranges)
                if (range.prefix == prefix && range.suffix == suffix && range.first == first && range.count == count) return &range;
            return nullptr;
        };
        const SymbolPatternRange* src = find_range(source_signature, mapping.source_prefix, mapping.source_suffix, mapping.source_first, mapping.count);
        const SymbolPatternRange* dst = find_range(target_signature, mapping.target_prefix, mapping.target_suffix, mapping.target_first, mapping.count);
        if (!src || !dst
            || (mapping.count != 0
                && (mapping.source_first > std::numeric_limits<std::uint64_t>::max() - (mapping.count - 1)
                    || mapping.target_first > std::numeric_limits<std::uint64_t>::max() - (mapping.count - 1)))
            || src->kind != dst->kind || src->domain.size() != dst->domain.size()
            || !H::sameSort(src->codomain, dst->codomain)) {
            diags.error(ErrorCode::E_INTERNAL, "semantic contract '" + id + "' has an unknown or ill-sorted symbol range mapping");
            ok = false;
            continue;
        }
        for (std::size_t i = 0; i < src->domain.size(); ++i)
            if (!H::sameSort(src->domain[i], dst->domain[i])) { ok = false; break; }
        if (src->domain.size() != dst->domain.size()) ok = false;
        for (const CoveredSymbolRange& previous : covered_ranges) {
            if (mapping.source_prefix != previous.prefix || mapping.source_suffix != previous.suffix || mapping.count == 0) continue;
            const auto end = mapping.source_first + mapping.count - 1;
            if (!(end < previous.first || mapping.source_first > previous.last)) {
                diags.error(ErrorCode::E_INTERNAL, "semantic contract '" + id + "' maps overlapping source symbol ranges");
                ok = false;
            }
        }
        if (mapping.count != 0)
            covered_ranges.push_back({mapping.source_prefix, mapping.source_suffix, mapping.source_first,
                                      mapping.source_first + mapping.count - 1});
    }
    if (claimed_fidelity.sound && claimed_fidelity.complete) {
        for (const SymbolPatternRange& range : source_signature.symbol_ranges) {
            const bool covered = std::any_of(symbol_range_map.begin(), symbol_range_map.end(), [&](const SymbolRangeMapping& mapping) {
                return mapping.source_prefix == range.prefix && mapping.source_suffix == range.suffix
                    && mapping.source_first == range.first && mapping.count == range.count;
            });
            if (!covered) {
                diags.error(ErrorCode::E_INTERNAL, "exact semantic contract '" + id + "' does not map source symbol range '" + range.prefix + "'");
                ok = false;
            }
        }
    }
    for (const ChoiceObservable& choice : projection.choices) {
        for (const ChoiceAlternative& alternative : choice.alternatives) {
            for (const ChoiceAlternative::Binding& binding : alternative.bindings) {
                const bool integer_binding =
                    binding.kind == ChoiceAlternative::Binding::Kind::INTEGER;
                const bool boolean_binding =
                    binding.kind == ChoiceAlternative::Binding::Kind::BOOLEAN;
                const bool bitvector_binding =
                    binding.kind == ChoiceAlternative::Binding::Kind::BITVECTOR;
                const bool smt_term_binding =
                    binding.kind == ChoiceAlternative::Binding::Kind::SMT_TERM;
                const bool smt_string_value_binding =
                    binding.kind == ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE;
                if ((!integer_binding && !boolean_binding && !bitvector_binding
                     && !smt_term_binding && !smt_string_value_binding)
                    || (bitvector_binding && binding.bit_width == 0)
                    || (!bitvector_binding && binding.bit_width != 0)) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "semantic contract '" + id
                                    + "' has a choice binding with an invalid kind or width");
                    ok = false;
                    continue;
                }
                const SymbolRange target_symbols = lookup(target_index, binding.target_name);
                if (target_symbols.empty() || target_symbols.size() != 1) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "semantic contract '" + id
                                    + "' has a choice binding to unknown target symbol '"
                                    + binding.target_name + "'");
                    ok = false;
                    continue;
                }
                const Symbol& target_symbol = *target_symbols.front();
                const H::Sort expected_sort =
                    binding.kind == ChoiceAlternative::Binding::Kind::INTEGER
                        ? H::Sort::integer()
                    : binding.kind == ChoiceAlternative::Binding::Kind::BOOLEAN
                        ? H::Sort::boolean()
                    : (binding.kind == ChoiceAlternative::Binding::Kind::SMT_TERM
                       || binding.kind == ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE)
                        ? H::Sort::string()
                        : H::Sort::bitvec(binding.bit_width);
                if (target_symbol.kind != SymbolKind::CONSTANT
                    || !target_symbol.domain.empty()
                    || !H::sameSort(target_symbol.codomain, expected_sort)) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "semantic contract '" + id
                                    + "' has a choice binding with the wrong target sort for '"
                                    + binding.target_name + "'");
                    ok = false;
                }
            }
        }
    }
    for (const GrammarChoiceObservable& grammar : projection.grammar_choices) {
        if (grammar.source_name.empty() || grammar.nodes.empty()
            || grammar.root_node >= grammar.nodes.size()) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + id
                            + "' has a malformed grammar projection root");
            ok = false;
            continue;
        }
        std::vector<unsigned char> marks(grammar.nodes.size(), 0);
        std::set<std::string> grammar_selector_names;
        bool valid_graph = true;
        for (const GrammarChoiceNode& node : grammar.nodes) {
            if ((node.selector_target.empty() && node.alternatives.size() != 1)
                || node.alternatives.empty()) {
                valid_graph = false;
                break;
            }
            for (const GrammarChoiceAlternative& alternative : node.alternatives) {
                std::set<std::string> child_names;
                bool placeholders_valid = true;
                for (const std::string& placeholder : alternative.child_placeholders) {
                    if (placeholder.empty()
                        || !child_names.insert(canonicalSmtSymbol(placeholder)).second) {
                        placeholders_valid = false;
                    }
                }
                std::set<std::string> binding_names;
                for (const ChoiceAlternative::Binding& binding : alternative.bindings) {
                    if (binding.placeholder.empty()
                        || !binding_names.insert(
                               canonicalSmtSymbol(binding.placeholder)).second) {
                        placeholders_valid = false;
                    }
                }
                if (alternative.children.size() != alternative.child_placeholders.size()
                    || alternative.label.empty()
                    || !placeholders_valid
                    || std::any_of(child_names.begin(), child_names.end(),
                                   [&](const std::string& child_name) {
                                       return binding_names.count(child_name) != 0;
                                   })
                    || std::any_of(alternative.children.begin(), alternative.children.end(),
                                   [&](std::size_t child) {
                                       return child >= grammar.nodes.size();
                                   })) {
                    valid_graph = false;
                    break;
                }
            }
            if (!valid_graph) { break; }
        }
        struct DfsFrame {
            std::size_t node;
            std::size_t alternative = 0;
            std::size_t child = 0;
        };
        std::vector<DfsFrame> dfs;
        for (std::size_t start = 0; valid_graph && start < grammar.nodes.size(); ++start) {
            if (marks[start] == 2) { continue; }
            marks[start] = 1;
            dfs.push_back({start, 0, 0});
            while (!dfs.empty()) {
                DfsFrame& frame = dfs.back();
                const auto& alternatives = grammar.nodes[frame.node].alternatives;
                if (frame.alternative == alternatives.size()) {
                    marks[frame.node] = 2;
                    dfs.pop_back();
                    continue;
                }
                const auto& children = alternatives[frame.alternative].children;
                if (frame.child == children.size()) {
                    ++frame.alternative;
                    frame.child = 0;
                    continue;
                }
                const std::size_t child = children[frame.child++];
                if (marks[child] == 1) {
                    valid_graph = false;
                    break;
                }
                if (marks[child] == 0) {
                    marks[child] = 1;
                    dfs.push_back({child, 0, 0});
                }
            }
            dfs.clear();
        }
        if (!valid_graph) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + id
                            + "' has a cyclic or malformed grammar projection");
            ok = false;
        }
        for (const GrammarChoiceNode& node : grammar.nodes) {
            if (!node.selector_target.empty()) {
                const SymbolRange selector_symbols = lookup(target_index, node.selector_target);
                if (!grammar_selector_names.insert(node.selector_target).second
                    || selector_symbols.empty() || selector_symbols.size() != 1
                    || selector_symbols.front()->kind != SymbolKind::CONSTANT
                    || !selector_symbols.front()->domain.empty()
                    || !H::sameSort(selector_symbols.front()->codomain,
                                    H::Sort::integer())) {
                    diags.error(ErrorCode::E_INTERNAL,
                                "semantic contract '" + id
                                    + "' has an invalid target grammar selector '"
                                    + node.selector_target + "'");
                    ok = false;
                }
            }
            for (const GrammarChoiceAlternative& alternative : node.alternatives) {
                for (const ChoiceAlternative::Binding& binding : alternative.bindings) {
                    const bool integer_binding =
                        binding.kind == ChoiceAlternative::Binding::Kind::INTEGER;
                    const bool boolean_binding =
                        binding.kind == ChoiceAlternative::Binding::Kind::BOOLEAN;
                    const bool bitvector_binding =
                        binding.kind == ChoiceAlternative::Binding::Kind::BITVECTOR;
                    const bool smt_term_binding =
                        binding.kind == ChoiceAlternative::Binding::Kind::SMT_TERM;
                    const bool smt_string_value_binding =
                        binding.kind == ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE;
                    if ((!integer_binding && !boolean_binding && !bitvector_binding
                         && !smt_term_binding && !smt_string_value_binding)
                        || (bitvector_binding && binding.bit_width == 0)
                        || (!bitvector_binding && binding.bit_width != 0)) {
                        diags.error(ErrorCode::E_INTERNAL,
                                    "semantic contract '" + id
                                        + "' has a grammar binding with an invalid kind or width");
                        ok = false;
                        continue;
                    }
                    const SymbolRange binding_symbols = lookup(target_index, binding.target_name);
                    if (binding_symbols.empty() || binding_symbols.size() != 1) {
                        diags.error(ErrorCode::E_INTERNAL,
                                    "semantic contract '" + id
                                        + "' has a grammar binding to unknown target symbol '"
                                        + binding.target_name + "'");
                        ok = false;
                        continue;
                    }
                    const Symbol& symbol = *binding_symbols.front();
                    const H::Sort expected = integer_binding ? H::Sort::integer()
                        : boolean_binding ? H::Sort::boolean()
                        : (smt_term_binding || smt_string_value_binding)
                            ? H::Sort::string()
                            : H::Sort::bitvec(binding.bit_width);
                    if (symbol.kind != SymbolKind::CONSTANT || !symbol.domain.empty()
                        || !H::sameSort(symbol.codomain, expected)) {
                        diags.error(ErrorCode::E_INTERNAL,
                                    "semantic contract '" + id
                                        + "' has a grammar binding with the wrong target sort");
                        ok = false;
                    }
                }
            }
        }
    }
    struct ObservableCoverage { std::string prefix; std::string suffix; std::uint64_t first; std::uint64_t last; };
    std::vector<ObservableCoverage> observable_coverage;
    const auto findSymbolPattern = [](const SignatureSnapshot& signature,
                                      const std::string& prefix, const std::string& suffix,
                                      std::uint64_t first, std::uint64_t count)
        -> const SymbolPatternRange* {
        if (count == 0 || first > std::numeric_limits<std::uint64_t>::max() - (count - 1)) return nullptr;
        const std::uint64_t last = first + count - 1;
        for (const SymbolPatternRange& candidate : signature.symbol_ranges) {
            if (candidate.prefix.empty() || candidate.count == 0
                || candidate.first > std::numeric_limits<std::uint64_t>::max() - (candidate.count - 1)) continue;
            if (prefix == candidate.prefix && suffix == candidate.suffix && first >= candidate.first
                && last <= candidate.first + candidate.count - 1) return &candidate;
        }
        return nullptr;
    };
    for (const ObservableRange& range : projection.observable_ranges) {
        const auto* src = findSymbolPattern(source_signature, range.source_prefix, range.source_suffix, range.source_first, range.count);
        const auto* dst = findSymbolPattern(target_signature, range.target_prefix, range.target_suffix, range.target_first, range.count);
        const bool direct_sort_match = src && dst
            && H::sameSort(src->codomain, dst->codomain);
        const bool bool_zero_one_match = src && dst
            && src->codomain.kind == H::SortKind::BOOL
            && dst->codomain.kind == H::SortKind::INT;
        if (!src || !dst || range.projection == ProjectionKind::CONSTANT
            || src->kind != SymbolKind::CONSTANT || dst->kind != SymbolKind::CONSTANT
            || (range.projection == ProjectionKind::DIRECT && !direct_sort_match)
            || (range.projection == ProjectionKind::BOOL_FROM_ZERO_ONE
                && !bool_zero_one_match)) {
            diags.error(ErrorCode::E_INTERNAL, "semantic contract '" + id + "' has an invalid observable symbol range");
            ok = false;
            continue;
        }
        for (const ObservableCoverage& prior : observable_coverage) {
            if (prior.prefix == range.source_prefix && prior.suffix == range.source_suffix
                && !(range.source_first + range.count - 1 < prior.first
                     || range.source_first > prior.last)) {
                diags.error(ErrorCode::E_INTERNAL, "semantic contract '" + id + "' has overlapping observable ranges");
                ok = false;
            }
        }
        observable_coverage.push_back({range.source_prefix, range.source_suffix, range.source_first,
                                       range.source_first + range.count - 1});
    }
    for (const Observable& optional : projection.optional_observables) {
        const SymbolRange optional_source = lookup(source_index, optional.source_name);
        const SymbolRange optional_target = lookup(target_index, optional.target_name);
        if (optional.source_name.empty() || optional.target_name.empty()
            || optional.projection != ProjectionKind::DIRECT
            || optional_source.empty() || optional_target.empty()
            || !namedSymbolsMap(*this, optional_source, optional_target)) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + id
                            + "' has an invalid optional target observable");
            ok = false;
        }
    }
    if (claimed_fidelity.sound && claimed_fidelity.complete) {
        for (const Symbol& symbol : source_signature.symbols) {
            if (mapped.count(symbol.name) == 0) {
                diags.error(ErrorCode::E_INTERNAL,
                            "exact semantic contract '" + id + "' does not map source symbol '"
                                + symbol.name + "'");
                ok = false;
            }
        }
    }
    std::vector<bool> bounded_symbols;
    if (!target_declaration_bounds.empty()) {
        bounded_symbols.resize(target_signature.symbols.size(), false);
    }
    for (const auto& axiom : target_declaration_bounds) {
        if (!validDeclarationBounds(axiom, target_signature)
            || bounded_symbols[axiom.target_symbol_index]) {
            diags.error(ErrorCode::E_INTERNAL, "semantic contract '" + id
                + "' contains an invalid compact declaration bound axiom", axiom.loc);
            ok = false;
        } else {
            bounded_symbols[axiom.target_symbol_index] = true;
        }
    }
    for (const H::ScalarVarRange& range : target_range_axioms) {
        const auto* symbol = findSymbolPattern(target_signature, range.prefix,
                                               range.suffix, range.first, range.count);
        const auto valid_bound = [](const H::ExprPtr& bound) {
            return !bound || (bound->kind == H::ExprKind::LIT_INT
                && bound->sort.kind == H::SortKind::INT);
        };
        if (!symbol || symbol->first != range.first || symbol->count != range.count
            || symbol->kind != SymbolKind::CONSTANT || !symbol->domain.empty()
            || range.prefix.empty() || range.prefix.back() != '[' || range.suffix != "]"
            || range.sort.kind != H::SortKind::INT || !H::sameSort(symbol->codomain, range.sort)
            || (!range.lower_bound && !range.upper_bound)
            || !valid_bound(range.lower_bound) || !valid_bound(range.upper_bound)) {
            diags.error(ErrorCode::E_INTERNAL, "semantic contract '" + id
                + "' contains an invalid compact scalar bound axiom", range.loc);
            ok = false;
        }
    }
    for (const Sentence& axiom : target_axioms) {
        if (!axiom || axiom->sort.kind != H::SortKind::BOOL) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + id
                            + "' contains a null or non-Boolean target axiom");
            ok = false;
        }
    }
    if (claimed_fidelity.sound
        && !hasRecordedEvidence(findObligation(*this, ProofObligationKind::SOUNDNESS))) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' claims soundness without recorded evidence for its obligation");
        ok = false;
    }
    if (claimed_fidelity.complete
        && !hasRecordedEvidence(findObligation(*this, ProofObligationKind::COMPLETENESS))) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' claims completeness without recorded evidence for its obligation");
        ok = false;
    }
    if (claimed_fidelity.count_status == CountStatus::PRESERVED
        && !hasRecordedCountEvidence(findObligation(*this, ProofObligationKind::MODEL_COUNT))) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' claims model-count preservation without concrete MODEL_COUNT evidence");
        ok = false;
    }
    if (claimed_fidelity.preserves_optimum
        && objectives.source != ObjectiveOrder::SATISFACTION
        && !hasRecordedEvidence(findObligation(*this, ProofObligationKind::OBJECTIVE))) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' claims optimum preservation without an objective obligation");
        ok = false;
    }
    if (!projection.observables.empty() || !projection.choices.empty()
        || !projection.grammar_choices.empty()
        || !projection.optional_observables.empty()
        || !projection.observable_ranges.empty()) {
        if (!hasRecordedEvidence(
                findObligation(*this, ProofObligationKind::OBSERVABLES))) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + id
                            + "' has a model projection without an observables obligation");
            ok = false;
        }
    }
    if (decision.target_sat_meaning.empty()
        || decision.target_unsat_meaning.empty()) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' does not define how target SAT and UNSAT map to its source question");
        ok = false;
    }
    if (claimed_fidelity.preserves_optimum
        && (!objectives.order_preserving || !objectives.order_reflecting)) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' claims optimum preservation but its objective map does not "
                          "preserve and reflect order");
        ok = false;
    }
    const bool source_has_objective =
        objectives.source != ObjectiveOrder::SATISFACTION;
    const bool target_has_objective =
        objectives.target != ObjectiveOrder::SATISFACTION;
    if (source_has_objective != !objectives.source_directions.empty()
        || target_has_objective != !objectives.target_directions.empty()) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' has objective directions inconsistent with its source or target order");
        ok = false;
    }
    if (objectives.value_map_id.empty()) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id + "' does not identify its objective value map h");
        ok = false;
    }
    if (claimed_fidelity.preserves_optimum
        && source_has_objective
        && objectives.source_directions.size()
               != objectives.target_directions.size()) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + id
                        + "' claims optimum preservation but changes the objective tuple arity");
        ok = false;
    }
    return ok;
}

bool validateSourceContract(const SourceSemanticSpec& specification,
                            const TranslationContract& contract,
                            Diagnostics& diags) {
    bool ok = true;
    if (!specification.valid()) {
        diags.error(ErrorCode::E_INTERNAL,
                    "the registered language has no valid source semantic specification");
        return false;
    }
    if (!sameInstitutionDefinition(contract.source, specification.institution)) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + contract.id
                        + "' does not start in the registered source Institution '"
                        + specification.institution.id + "'");
        ok = false;
    }
    if (!specification.supports(contract.decision.source)) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + contract.id
                        + "' selects a decision problem not admitted by its source language");
        ok = false;
    }
    if (specification.smt_embedding
        == SmtEmbeddingKind::NO_DIRECT_FIRST_ORDER_REDUCTION) {
        diags.error(ErrorCode::E_INTERNAL,
                    "semantic contract '" + contract.id
                        + "' claims a direct SMT pipeline for a source language whose "
                          "semantic specification forbids that reduction");
        ok = false;
    }
    auto required_bounds = specification.required_bounds;
    const auto selected_bounds = specification.decision_bounds.find(contract.decision.source);
    if (selected_bounds != specification.decision_bounds.end()) {
        required_bounds.insert(required_bounds.end(), selected_bounds->second.begin(),
                               selected_bounds->second.end());
    }
    for (const Fidelity::Bound::Kind required : required_bounds) {
        bool found = false;
        for (const Fidelity::Bound& actual : contract.claimed_fidelity.bounds) {
            if (actual.kind == required) {
                found = true;
                break;
            }
        }
        if (!found) {
            // Exact unbounded SyGuS encodings quantify over the inductive AST
            // of every finite derivation. The source specification keeps the
            // grammar-restriction requirement for bounded encodings, but a
            // complete contract does not have a depth cutoff to report.
            const bool exact_unbounded_sygus =
                specification.institution.id == "sygus"
                && required == Fidelity::Bound::GRAMMAR_RESTRICTION
                && contract.claimed_fidelity.sound
                && contract.claimed_fidelity.complete
                && contract.claimed_fidelity.bounds.empty();
            if (exact_unbounded_sygus) { continue; }
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic contract '" + contract.id
                            + "' omits a bound required by its source semantic specification");
            ok = false;
        }
    }
    return ok;
}

void TranslationPipeline::add(TranslationContract contract) {
    stages_.push_back(std::move(contract));
}

bool TranslationPipeline::validate(Diagnostics& diags) const {
    bool ok = true;
    for (std::size_t i = 0; i < stages_.size(); ++i) {
        ok = stages_[i].validate(diags) && ok;
        if (i != 0
            && (!sameInstitutionDefinition(stages_[i - 1].target, stages_[i].source)
                || !sameSignature(stages_[i - 1].target_signature,
                                  stages_[i].source_signature)
                || stages_[i - 1].objectives.target != stages_[i].objectives.source
                || stages_[i - 1].objectives.target_directions
                       != stages_[i].objectives.source_directions
                || stages_[i - 1].decision.target != stages_[i].decision.source)) {
            diags.error(ErrorCode::E_INTERNAL,
                        "semantic pipeline is not composable between '"
                            + stages_[i - 1].id + "' and '" + stages_[i].id + "'");
            ok = false;
        }
    }
    return ok;
}

bool TranslationPipeline::project(const Assignment& target, Assignment& source,
                                  Diagnostics& diags) const {
    Assignment current = target;
    for (auto stage = stages_.rbegin(); stage != stages_.rend(); ++stage) {
        Assignment projected;
        if (!stage->projection.project(current, projected, diags)) { return false; }
        current = std::move(projected);
    }
    source = std::move(current);
    return true;
}

Fidelity TranslationPipeline::fidelity() const {
    Fidelity result = Fidelity::exact();
    bool has_stage = false;
    for (const TranslationContract& stage : stages_) {
        if (!has_stage) {
            result = stage.claimed_fidelity;
            has_stage = true;
        } else {
            result = Fidelity::meet(result, stage.claimed_fidelity);
        }
    }
    return result;
}

bool TranslationPipeline::targetSatMeansSourceYes() const noexcept {
    bool preserves = true;
    for (const TranslationContract& stage : stages_) {
        if (stage.decision.polarity == VerdictPolarity::INVERT) {
            preserves = !preserves;
        }
    }
    return preserves;
}

PartialExpr RelationalBuilder::total(H::ExprPtr value) const {
    return {H::mkBool(true, value ? value->loc : SourceLoc{}), std::move(value)};
}

PartialExpr RelationalBuilder::inspect(const H::ExprPtr& value) const {
    if (!value) { return {nullptr, nullptr}; }
    const auto it = definitions_.find(value);
    return {it == definitions_.end() ? H::mkBool(true, value->loc) : it->second, value};
}

H::ExprPtr RelationalBuilder::remember(PartialExpr expression) {
    if (!expression.value || !expression.defined) { return nullptr; }
    if (!isBoolLiteral(expression.defined, true)) {
        definitions_[expression.value] = expression.defined;
    } else {
        definitions_.erase(expression.value);
    }
    return expression.value;
}

H::ExprPtr RelationalBuilder::conjunction(std::vector<H::ExprPtr> terms,
                                          SourceLoc loc) {
    std::vector<H::ExprPtr> kept;
    kept.reserve(terms.size());
    for (H::ExprPtr& term : terms) {
        if (!term || isBoolLiteral(term, true)) { continue; }
        if (isBoolLiteral(term, false)) { return H::mkBool(false, term->loc); }
        kept.push_back(std::move(term));
    }
    if (kept.empty()) { return H::mkBool(true, std::move(loc)); }
    if (kept.size() == 1) { return kept.front(); }
    return H::mkOp(H::Op::AND, std::move(kept), std::move(loc));
}

H::ExprPtr RelationalBuilder::attach(H::ExprPtr raw,
                                     const std::vector<H::ExprPtr>& inputs,
                                     H::ExprPtr domain) {
    if (!raw) { return nullptr; }
    // Most parameter reads have only total inputs. Allocate guard storage
    // only when an input actually contributes a partiality condition.
    std::vector<H::ExprPtr> definitions;
    for (const H::ExprPtr& input : inputs) {
        const auto found = definitions_.find(input);
        if (found != definitions_.end()) { definitions.push_back(found->second); }
    }
    if (domain && !isBoolLiteral(domain, true)) {
        definitions.push_back(std::move(domain));
    }
    if (definitions.empty()) {
        // attach() replaces the raw node's previous definition. In particular,
        // a reused node may become total after its former guard is discharged.
        // Inspect inputs first: raw itself may be one of the partial inputs.
        definitions_.erase(raw);
        return raw;
    }
    const SourceLoc at = raw->loc;
    return remember({conjunction(std::move(definitions), at), std::move(raw)});
}

H::ExprPtr RelationalBuilder::value(H::Op op,
                                    const std::vector<H::ExprPtr>& args,
                                    SourceLoc loc, H::ExprPtr domain) {
    return attach(H::mkOp(op, args, loc), args, std::move(domain));
}

H::ExprPtr RelationalBuilder::relation(H::ExprPtr raw_relation,
                                       const std::vector<H::ExprPtr>& inputs,
                                       H::ExprPtr domain) {
    std::vector<H::ExprPtr> terms;
    terms.reserve(inputs.size() + 2);
    for (const H::ExprPtr& input : inputs) {
        const auto found = definitions_.find(input);
        if (found != definitions_.end()) { terms.push_back(found->second); }
    }
    if (domain) { terms.push_back(std::move(domain)); }
    terms.push_back(std::move(raw_relation));
    return remember(total(conjunction(std::move(terms))));
}

H::ExprPtr RelationalBuilder::predicate(H::Op op,
                                        const std::vector<H::ExprPtr>& args,
                                        SourceLoc loc, H::ExprPtr domain) {
    return relation(H::mkOp(op, args, loc), args, std::move(domain));
}

H::ExprPtr RelationalBuilder::boolean(H::Op op,
                                      const std::vector<H::ExprPtr>& args,
                                      SourceLoc loc) {
    std::vector<H::ExprPtr> values;
    values.reserve(args.size());
    for (const H::ExprPtr& arg : args) { values.push_back(require(arg)); }
    return remember(total(H::mkOp(op, std::move(values), std::move(loc))));
}

H::ExprPtr RelationalBuilder::conditional(const H::ExprPtr& condition,
                                          const H::ExprPtr& when_true,
                                          const H::ExprPtr& when_false,
                                          SourceLoc loc) {
    const PartialExpr c = inspect(condition);
    const PartialExpr t = inspect(when_true);
    const PartialExpr f = inspect(when_false);
    if (!c.value || !t.value || !f.value) { return nullptr; }
    // Preserve totality when both branches are total. Keeping an unsimplified
    // ite(c, true, true) here makes remember() retain a total temporary and
    // its entire value DAG as if it had a nontrivial partiality predicate.
    // Also select a fixed condition's guard without evaluating its other
    // branch. The condition's own definedness is still conjoined below.
    H::ExprPtr selected_definition;
    if (isBoolLiteral(c.value, true)) {
        selected_definition = t.defined;
    } else if (isBoolLiteral(c.value, false)) {
        selected_definition = f.defined;
    } else if (t.defined == f.defined
               || (isBoolLiteral(t.defined, true) && isBoolLiteral(f.defined, true))
               || (isBoolLiteral(t.defined, false) && isBoolLiteral(f.defined, false))) {
        selected_definition = t.defined;
    } else {
        selected_definition = H::mkOp(
            H::Op::ITE, {c.value, t.defined, f.defined}, loc);
    }
    H::ExprPtr definition = conjunction(
        {c.defined, std::move(selected_definition)}, loc);
    H::ExprPtr value = H::mkOp(
        H::Op::ITE, {c.value, t.value, f.value}, loc);
    return remember({std::move(definition), std::move(value)});
}

H::ExprPtr RelationalBuilder::fallback(const H::ExprPtr& first,
                                       const H::ExprPtr& otherwise,
                                       SourceLoc loc) {
    const PartialExpr a = inspect(first);
    const PartialExpr b = inspect(otherwise);
    if (!a.value || !b.value) { return nullptr; }
    if (!H::sameSort(a.value->sort, b.value->sort)) { return nullptr; }
    if (isBoolLiteral(a.defined, true)) { return first; }
    if (isBoolLiteral(a.defined, false)) { return otherwise; }
    H::ExprPtr defined = isBoolLiteral(b.defined, true)
        ? H::mkBool(true, loc)
        : H::mkOp(H::Op::OR, {a.defined, b.defined}, loc);
    H::ExprPtr value = H::mkOp(H::Op::ITE,
                               {a.defined, a.value, b.value}, loc);
    return remember({std::move(defined), std::move(value)});
}

H::ExprPtr RelationalBuilder::require(const H::ExprPtr& boolean_expression) const {
    const PartialExpr expression = inspect(boolean_expression);
    if (!expression.value) { return nullptr; }
    return conjunction({expression.defined, expression.value}, expression.value->loc);
}

namespace {

Institution miniZincInstitution() {
    return {"minizinc", "MiniZinc", "typed first-order constraint language",
            "declarative constraint semantics", "well-typed elaborated MiniZinc expressions",
            "MiniZinc assignments satisfying type-inst domains",
            "MiniZinc specification evaluation with relational partiality",
            AssumptionProfile::miniZinc()};
}

Institution flatZincInstitution() {
    return {"flatzinc", "FlatZinc", "flat typed relational constraint language",
            "constraint satisfaction with solve-item optimization",
            "well-typed FlatZinc declarations and builtin constraints",
            "FlatZinc assignments over declared variable domains",
            "every builtin relation holds and every partial builtin is defined",
            AssumptionProfile::flatZinc()};
}

Institution essencePrimeInstitution() {
    return {"essence-prime", "Essence Prime",
            "finite-domain typed constraint language",
            "parameter instantiation followed by finite constraint satisfaction",
            "instantiated, well-typed Essence Prime expressions",
            "assignments to find-declared values and finite matrix cells",
            "all such-that constraints hold under relational undefinedness",
            AssumptionProfile::essencePrime()};
}

Institution xcsp3Institution() {
    return {"xcsp3", "XCSP3-core", "finite-domain relational constraint language",
            "CSP/COP satisfaction over explicitly declared finite domains",
            "XCSP3-core constraints and objective expressions",
            "assignments to XCSP3 integer variables",
            "all declared domains and constraints hold under XCSP3 operator evaluation",
            AssumptionProfile::xcsp3()};
}

AssumptionProfile finiteBooleanProfile(const std::string& id,
                                       QuantifierSemantics quantifiers,
                                       AnnotationSemantics annotations =
                                           AnnotationSemantics::NONE) {
    AssumptionProfile p;
    p.id = id;
    p.carriers = CarrierSemantics::FINITE;
    p.carrier_emptiness = CarrierEmptiness::NONEMPTY;
    p.functions = FunctionSemantics::TOTAL;
    p.undefined = UndefinedSemantics::ERROR;
    p.arithmetic = ArithmeticSemantics::NONE;
    p.overflow = OverflowSemantics::UNBOUNDED;
    p.division = DivisionSemantics::MIXED;
    p.arrays = ArraySemantics::NONE;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = quantifiers;
    p.invalid_phase = PhaseSemantics::STATIC_ERROR;
    p.annotations = annotations;
    return p;
}

AssumptionProfile pseudoBooleanProfile(const std::string& id) {
    AssumptionProfile p = finiteBooleanProfile(
        id, QuantifierSemantics::NONE, AnnotationSemantics::MIXED);
    p.arithmetic = ArithmeticSemantics::INTEGER;
    return p;
}

AssumptionProfile planningProfile(const std::string& id) {
    auto p = finiteBooleanProfile(id, QuantifierSemantics::FINITE_EXPANSION,
                                   AnnotationSemantics::SEMANTIC);
    p.carriers = CarrierSemantics::MIXED; // finite objects, unbounded accumulated cost
    p.carrier_emptiness = CarrierEmptiness::MIXED; // object types can have no instances
    p.arithmetic = ArithmeticSemantics::RATIONAL;
    p.division = DivisionSemantics::EXACT_REAL;
    return p;
}

AssumptionProfile linearOptimizationProfile(const std::string& id) {
    AssumptionProfile p;
    p.id = id;
    p.carriers = CarrierSemantics::MIXED;
    p.carrier_emptiness = CarrierEmptiness::NONEMPTY;
    p.functions = FunctionSemantics::TOTAL;
    p.undefined = UndefinedSemantics::ERROR;
    p.arithmetic = ArithmeticSemantics::MIXED;
    p.overflow = OverflowSemantics::UNBOUNDED;
    p.division = DivisionSemantics::EXACT_REAL;
    p.arrays = ArraySemantics::NONE;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::NONE;
    p.invalid_phase = PhaseSemantics::STATIC_ERROR;
    p.annotations = AnnotationSemantics::MIXED;
    return p;
}

AssumptionProfile transitionProfile(const std::string& id, bool word_level) {
    AssumptionProfile p = finiteBooleanProfile(
        id, QuantifierSemantics::NONE, AnnotationSemantics::SEMANTIC);
    if (word_level) {
        p.arithmetic = ArithmeticSemantics::BIT_VECTOR;
        p.overflow = OverflowSemantics::MODULAR;
        p.arrays = ArraySemantics::TOTAL_EXTENSIONAL;
    }
    return p;
}

AssumptionProfile smtTransitionProfile(const std::string& id) {
    AssumptionProfile p = AssumptionProfile::smtLib();
    p.id = id;
    p.annotations = AnnotationSemantics::SEMANTIC;
    return p;
}

AssumptionProfile boogieProfile() {
    AssumptionProfile p = AssumptionProfile::smtLib();
    p.id = "boogie-2-verification";
    p.invalid_phase = PhaseSemantics::STATIC_ERROR;
    p.annotations = AnnotationSemantics::STRATEGY_ONLY;
    return p;
}

AssumptionProfile cryptoLineProfile() {
    AssumptionProfile p;
    p.id = "cryptoline-bit-precise-core";
    p.carriers = CarrierSemantics::MIXED;
    p.carrier_emptiness = CarrierEmptiness::NONEMPTY;
    p.functions = FunctionSemantics::TOTAL;
    p.undefined = UndefinedSemantics::ERROR;
    p.arithmetic = ArithmeticSemantics::MIXED;
    p.overflow = OverflowSemantics::MODULAR;
    p.division = DivisionSemantics::MIXED;
    p.arrays = ArraySemantics::NONE;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::NONE;
    p.invalid_phase = PhaseSemantics::STATIC_ERROR;
    p.annotations = AnnotationSemantics::STRATEGY_ONLY;
    return p;
}

AssumptionProfile firstOrderProfile(const std::string& id) {
    AssumptionProfile p;
    p.id = id;
    p.carriers = CarrierSemantics::MIXED;
    p.carrier_emptiness = CarrierEmptiness::NONEMPTY;
    p.functions = FunctionSemantics::TOTAL;
    p.undefined = UndefinedSemantics::ERROR;
    p.arithmetic = ArithmeticSemantics::NONE;
    p.overflow = OverflowSemantics::UNBOUNDED;
    p.division = DivisionSemantics::MIXED;
    p.arrays = ArraySemantics::NONE;
    p.equality = EqualitySemantics::EXTENSIONAL;
    p.quantifiers = QuantifierSemantics::NATIVE;
    p.invalid_phase = PhaseSemantics::STATIC_ERROR;
    p.annotations = AnnotationSemantics::NONE;
    return p;
}

Institution directSourceInstitution(const std::string& id) {
    if (id == "aiger") {
        return {id, "AIGER 1.9", "Boolean sequential circuits with bad states",
                "unbounded safety over all initialized traces",
                "an AIGER circuit with reset, transition, constraint and bad-state relations",
                "initialized infinite input and latch traces",
                "the trace obeys reset, transition and constraints and avoids every bad state at every step",
                transitionProfile("aiger-1.9-safety", false)};
    }
    if (id == "btor2") {
        return {id, "BTOR2", "word-level bit-vector/array transition systems",
                "unbounded safety over initialized word-level traces",
                "a BTOR2 transition system with bad-state properties",
                "initialized infinite state and input traces",
                "the trace obeys init, next and constraint nodes and avoids every bad state",
                transitionProfile("btor2-transition-system", true)};
    }
    if (id == "vmt") {
        return {id, "VMT-LIB", "SMT-theory symbolic transition systems",
                "unbounded invariant safety over symbolic traces",
                "annotated :init, :trans and :invar-property terms",
                "theory interpretations with reachability generated by finite initialized paths",
                "every finite path obeys init/trans and every reachable state satisfies every invariant property",
                smtTransitionProfile("vmt-lib-transition-system")};
    }
    if (id == "moxi") {
        return {id, "MoXI", "hierarchical SMT-theory transition systems",
                "unbounded reachability under a selected check-system query",
                "a hierarchical system and one selected check-system query",
                "flattened finite system traces of arbitrary length",
                "all selected assumptions hold and every selected reachable condition occurs",
                smtTransitionProfile("moxi-reachability")};
    }
    if (id == "boogie") {
        return {id, "Boogie", "typed imperative verification language",
                "verification-condition refutation",
                "accepted procedure bodies, contracts, axioms and proof obligations",
                "counterexample executions represented by SSA valuations",
                "a source execution satisfies the assumptions and violates an obligation",
                boogieProfile()};
    }
    if (id == "cryptoline") {
        return {id, "CryptoLine", "bit-precise straight-line program logic",
                "algebraic and range postcondition refutation",
                "typed instructions, hypotheses and proof obligations",
                "bit-vector SSA executions with signed/unsigned integer lifts",
                "the execution obeys instruction semantics and violates an obligation",
                cryptoLineProfile()};
    }
    if (id == "chc") {
        AssumptionProfile p = AssumptionProfile::smtLib();
        p.id = "chc-comp-format-2023-03-31";
        return {id, "CHC-COMP", "constrained Horn clauses over SMT theories",
                "existential predicate interpretation with universal clause closure",
                "Horn rules plus a false-headed query clause",
                "interpretations of the declared relation symbols",
                "every universally closed Horn clause is true",
                std::move(p)};
    }
    if (id == "tptp") {
        AssumptionProfile p;
        p.id = "tptp-9.3-classical-cnf-fof-tff-txf-thf0";
        p.carriers = CarrierSemantics::MIXED;
        p.carrier_emptiness = CarrierEmptiness::NONEMPTY;
        p.functions = FunctionSemantics::TOTAL;
        p.undefined = UndefinedSemantics::ERROR;
        p.arithmetic = ArithmeticSemantics::MIXED;
        p.overflow = OverflowSemantics::TARGET_DEFINED;
        p.division = DivisionSemantics::MIXED;
        p.arrays = ArraySemantics::NONE;
        p.equality = EqualitySemantics::EXTENSIONAL;
        p.quantifiers = QuantifierSemantics::NATIVE;
        p.invalid_phase = PhaseSemantics::STATIC_ERROR;
        p.annotations = AnnotationSemantics::STRATEGY_ONLY;
        return {id, "TPTP 9.3", "classical CNF/FOF/TFF/TXF and typed THF0 under Henkin semantics",
                "formula satisfaction or refutation of positive conjectures",
                "typed or untyped TPTP annotated formulas with role semantics",
                "first-order interpretations or nonempty simple-type Henkin domains, as selected by the frontend",
                "all non-conjecture formulas hold; positive conjectures are refuted as one combined obligation",
                std::move(p)};
    }
    if (id == "pddl") {
        auto assumptions = planningProfile("pddl-numeric-continuous-temporal");
        // Boolean atoms obey the closed-world convention; numeric fluents
        // have a separate definedness component. Undefined arithmetic must
        // propagate even through a Boolean branch whose value is redundant.
        assumptions.arithmetic = ArithmeticSemantics::REAL;
        assumptions.quantifiers = QuantifierSemantics::MIXED;
        assumptions.functions = FunctionSemantics::MIXED;
        assumptions.undefined = UndefinedSemantics::STRICT;
        assumptions.invalid_phase = PhaseSemantics::MIXED;
        return {id, "PDDL typed ADL, numeric, derived, continuous temporal and FOND fragments",
                "finite objects with partial real numeric state, exact trajectories and rationally timed transitions",
                "plan or policy existence with explicit numeric definedness, rational plan timestamps and outcome fairness",
                "a typed domain/problem pair with Boolean and numeric conditions/effects, positive derived rules, durative actions with discrete and continuous numeric effects, timed initial literals, metrics or optional oneof outcomes",
                "finite rationally timed action traces with exact real trajectories and pointwise least-fixed-point derived facts, or state-feedback policies closed under all outcomes",
                "a trace respects preconditions, simultaneous effects, frame axioms, simultaneous differential equations, full-interval conditions, endpoint interference and timed initial facts and reaches a stable goal; a policy reaches the goal under its selected strong or strong-cyclic semantics",
                std::move(assumptions)};
    }
    if (id == "dimacs") {
        return {id, "DIMACS CNF", "propositional logic in conjunctive normal form",
                "SAT over the header-declared Boolean vocabulary",
                "header plus a conjunction of clauses", "Boolean assignments",
                "every clause contains a true literal",
                finiteBooleanProfile("dimacs-cnf", QuantifierSemantics::NONE)};
    }
    if (id == "wcnf") {
        return {id, "Weighted CNF", "weighted partial MaxSAT",
                "lexicographic feasibility then minimum violated-clause weight",
                "hard and weighted soft clauses", "Boolean assignments with cost",
                "all hard clauses hold; cost is the weighted sum of violated soft clauses",
                finiteBooleanProfile("wcnf-maxsat", QuantifierSemantics::NONE)};
    }
    if (id == "opb") {
        return {id, "OPB/WBO", "pseudo-Boolean constraint optimization",
                "0-1 integer satisfaction with optional weighted violations",
                "pseudo-Boolean inequalities and objective", "0-1 assignments with cost",
                "all hard inequalities hold and the declared cost is ordered",
                pseudoBooleanProfile("opb-wbo-2.x")};
    }
    if (id == "lp") {
        return {id, "LP", "linear and mixed-integer optimization",
                "ordered-field linear constraints with declared integrality",
                "LP rows, bounds, variable kinds, and objective",
                "real/integer assignments with objective values",
                "all rows and bounds hold and the objective order is respected",
                linearOptimizationProfile("lp-cplex-syntax")};
    }
    if (id == "mps") {
        return {id, "MPS", "linear and mixed-integer optimization",
                "section-based linear constraints with bounds and integrality markers",
                "materialized MPS rows, columns, bounds, and objective",
                "real/integer assignments with objective values",
                "all selected RHS/bounds sets hold and the objective order is respected",
                linearOptimizationProfile("mps-fixed-free")};
    }
    if (id == "qcir") {
        return {id, "QCIR-G14", "quantified Boolean circuits",
                "QBF satisfaction with free variables and scoped circuit gates",
                "a quantified Boolean circuit rooted at output", "free assignments and QBF strategies",
                "the quantified output circuit evaluates to true",
                finiteBooleanProfile("qcir-g14", QuantifierSemantics::NATIVE)};
    }
    if (id == "qdimacs") {
        return {id, "QDIMACS", "prenex quantified Boolean CNF",
                "QBF truth under the ordered quantifier prefix",
                "an ordered prefix over one conjunctive clause matrix", "QBF strategies",
                "the prefixed matrix evaluates to true",
                finiteBooleanProfile("qdimacs-1.1", QuantifierSemantics::NATIVE)};
    }
    if (id == "smtlib2") {
        return {id, "SMT-LIB 2", "many-sorted first-order theories",
                "SMT-LIB model-theoretic semantics", "well-sorted SMT-LIB assertions",
                "SMT-LIB interpretations", "the interpretation satisfies every assertion",
                AssumptionProfile::smtLib()};
    }
    return {};
}

Institution hddlInstitution() {
    return {"hddl", "HDDL 1.0", "finite hierarchical task-network planning",
            "plan existence and bounded cost optimization by method decomposition and state transition",
            "a grounded domain/problem pair with an initial task network",
            "finite decomposition trees with executable primitive actions and method prefix events",
            "the root decomposes by declared methods; the full event trace reaches the goal and carries its exact accumulated cost",
            planningProfile("hddl-with-rational-costs")};
}

Institution sygusInstitution() {
    AssumptionProfile p = AssumptionProfile::smtLib();
    p.id = "sygus-if-2.1";
    p.annotations = AnnotationSemantics::SEMANTIC;
    return {"sygus", "SyGuS-IF 2.1",
            "grammar-constrained second-order function synthesis",
            "existential synthesis over grammar terms with universal semantic constraints",
            "synthesis declarations, grammars, universally scoped variables and constraints",
            "source function definitions derivable from the declared grammars",
            "substituting the definitions makes every constraint valid for all declared variables",
            std::move(p)};
}

Institution syntcompInstitution() {
    AssumptionProfile p = transitionProfile(
        "syntcomp-reactive-game", false);
    p.quantifiers = QuantifierSemantics::NATIVE;
    return {"syntcomp", "SYNTCOMP",
            "reactive temporal games with environment/system move partition",
            "winning-strategy existence over infinite or controller-terminated finite plays",
            "a safety circuit or temporal assume/guarantee specification",
            "causal controller strategies mapping observation histories to system moves",
            "every play induced by the strategy against every environment behavior satisfies the specification",
            std::move(p)};
}

DecisionKind coreDecision(const H::ConstraintModel& model) {
    return hasOptimization(model) ? DecisionKind::OPTIMIZATION
                                  : DecisionKind::SATISFIABILITY;
}

DecisionMapping sourceDecision(const std::string& id,
                               const H::ConstraintModel& model) {
    DecisionMapping mapping;
    mapping.target = coreDecision(model);
    mapping.source = mapping.target;
    mapping.target_sat_meaning =
        hasOptimization(model)
            ? "a feasible target model exists and carries the represented objective value"
            : "a target model exists and decodes to a source model";
    mapping.target_unsat_meaning = "no target model exists";

    if (id == "qcir" || id == "qdimacs") {
        mapping.source = DecisionKind::QBF_TRUTH;
        mapping.target_sat_meaning = "the quantified Boolean sentence is true";
        mapping.target_unsat_meaning = "the quantified Boolean sentence is false";
    } else if (id == "chc") {
        mapping.source = DecisionKind::HORN_SATISFIABILITY;
        mapping.target_sat_meaning = "a predicate interpretation satisfying all Horn clauses exists";
        mapping.target_unsat_meaning = "no predicate interpretation satisfies the Horn clauses";
    } else if (id == "aiger" || id == "btor2" || id == "vmt") {
        mapping.source = DecisionKind::SAFETY;
        mapping.polarity = VerdictPolarity::INVERT;
        mapping.target_sat_meaning = "a real bounded counterexample exists, so the safety claim is false";
        mapping.target_unsat_meaning = "no counterexample exists within the recorded bound; global safety is not established";
    } else if (id == "moxi") {
        mapping.source = DecisionKind::REACHABILITY;
        mapping.target_sat_meaning = "a real finite trace satisfies every selected reachability condition";
        mapping.target_unsat_meaning = "no such trace exists within the recorded bound";
    } else if (id == "boogie" || id == "cryptoline") {
        mapping.source = DecisionKind::PROGRAM_VERIFICATION;
        mapping.polarity = VerdictPolarity::INVERT;
        mapping.target_sat_meaning = "a counterexample execution violates a proof obligation";
        mapping.target_unsat_meaning = "no counterexample exists for the encoded verification conditions";
    } else if (id == "pddl" || id == "hddl") {
        mapping.source = hasOptimization(model) ? DecisionKind::OPTIMIZATION : DecisionKind::PLAN_EXISTENCE;
        mapping.target_sat_meaning =
            id == "hddl"
                ? "a source-valid hierarchical plan exists within both recorded bounds"
                : "a source-valid plan exists at the recorded horizon";
        mapping.target_unsat_meaning =
            id == "hddl"
                ? "no hierarchical plan exists within the plan and decomposition bounds"
                : "no plan exists at the recorded horizon";
        if (hasOptimization(model)) {
            mapping.target_sat_meaning += "; its accumulated cost is preserved, with optimization "
                "restricted to the recorded bounds";
        }
    } else if (id == "sygus") {
        mapping.source = DecisionKind::FUNCTION_SYNTHESIS;
        mapping.target_sat_meaning =
            "the selected grammar-derived definition satisfies every universally "
            "closed source constraint";
        mapping.target_unsat_meaning =
            "no definition exists within the grammar search scope represented by the "
            "translation";
    } else if (id == "syntcomp") {
        mapping.source = DecisionKind::REACTIVE_REALIZABILITY;
        mapping.target_sat_meaning =
            "the projected controller is a winning strategy for the accepted game";
        mapping.target_unsat_meaning =
            "no winning strategy exists in the accepted finite game model";
    }
    return mapping;
}

Institution relationalInstitution() {
    return {"typed-relational-core", "Typed Relational Optimization Core",
            "many-sorted relational constraint logic with objectives",
            "institutional satisfaction and model projection",
            "typed HIR relations with explicit definition predicates",
            "typed assignments extended by auxiliary relation witnesses",
            "defined predicates and relation values evaluate to true",
            AssumptionProfile::typedRelationalCore()};
}

Institution smtInstitution(bool optimization) {
    return {optimization ? "omt" : "smt-lib",
            optimization ? "Optimization Modulo Theories" : "SMT-LIB",
            optimization ? "many-sorted first-order theories with objectives"
                         : "many-sorted first-order theories",
            "SMT-LIB model-theoretic semantics",
            "well-sorted SMT-LIB assertions",
            optimization ? "SMT models paired with ordered objective values"
                         : "SMT-LIB interpretations",
            optimization ? "all assertions hold and the objective tuple is ordered"
                         : "the SMT-LIB interpretation satisfies every assertion",
            optimization ? AssumptionProfile::omt() : AssumptionProfile::smtLib()};
}

void addSortAndComponents(const H::Sort& sort, std::vector<SortMapping>& mappings) {
    for (const SortMapping& mapping : mappings) {
        if (H::sameSort(mapping.source, sort)) { return; }
    }
    mappings.push_back({sort, sort});
    if (sort.index) { addSortAndComponents(*sort.index, mappings); }
    if (sort.elem) { addSortAndComponents(*sort.elem, mappings); }
    for (const auto& argument : sort.args) {
        if (argument) { addSortAndComponents(*argument, mappings); }
    }
}

void addDirectSymbolsAndObservables(const H::ConstraintModel& model,
                                    TranslationContract& contract,
                                    bool auxiliaries_are_target_only = true,
                                    bool direct_observables = true,
                                    bool direct_source_symbols = true,
                                    const std::vector<H::ExprPtr>& declaration_terms = {},
                                    const std::vector<H::ExprPtr>& bound_axiom_hints = {},
                                    const SignatureSnapshot* postpass_signature_hint = nullptr) {
    if (postpass_signature_hint
        && signatureMatchesModel(*postpass_signature_hint, model)) {
        contract.target_signature = *postpass_signature_hint;
    } else {
        contract.target_signature = SignatureSnapshot(signatureOf(model));
    }
    // Planning adapters already own their source signature and alpha map.
    // Do not allocate an identity copy only to replace it immediately.
    if (direct_source_symbols) {
        std::set<std::string> auxiliary_names;
        if (auxiliaries_are_target_only) {
            for (const H::VarDecl& declaration : model.decls) {
                if (declaration.auxiliary) { auxiliary_names.insert(declaration.name); }
            }
            for (const H::FunDecl& declaration : model.funs) {
                if (declaration.auxiliary) { auxiliary_names.insert(declaration.name); }
            }
        }
        std::size_t source_count = 0;
        bool saw_auxiliary = false;
        bool auxiliaries_are_suffix = true;
        for (const Symbol& symbol : contract.target_signature.symbols) {
            if (auxiliary_names.find(symbol.name) != auxiliary_names.end()) {
                saw_auxiliary = true;
            } else {
                ++source_count;
                if (saw_auxiliary) { auxiliaries_are_suffix = false; }
            }
        }
        const bool filter_auxiliaries = auxiliaries_are_target_only
            && !auxiliary_names.empty();
        if (!filter_auxiliaries) {
            // The stage's source and target signatures are identical. Keep
            // one immutable backing store instead of copying every Symbol.
            contract.source_signature = contract.target_signature;
        } else if (auxiliaries_are_suffix) {
            // Packed objectives append a small auxiliary suffix. Excluding
            // it must not copy every source symbol and sort merely to shorten
            // an immutable signature. The two views remain distinct, so
            // validation cannot mistake their different domains for identity.
            contract.source_signature = contract.target_signature.symbolPrefix(source_count);
        } else {
            Signature source;
            source.sort_constructors.assign(
                contract.target_signature.sort_constructors.begin(),
                contract.target_signature.sort_constructors.end());
            source.symbol_ranges.assign(contract.target_signature.symbol_ranges.begin(),
                                        contract.target_signature.symbol_ranges.end());
            source.symbols.reserve(source_count);
            for (const Symbol& symbol : contract.target_signature.symbols) {
                if (auxiliary_names.find(symbol.name) == auxiliary_names.end()) {
                    source.symbols.push_back(symbol);
                }
            }
            contract.source_signature = SignatureSnapshot(std::move(source));
        }
        std::unordered_set<std::string_view> mapped;
        mapped.reserve(contract.source_signature.symbols.size());
        contract.symbol_map.reserve(
            contract.symbol_map.size() + contract.source_signature.symbols.size());
        for (const Symbol& symbol : contract.source_signature.symbols) {
            if (mapped.insert(symbol.name).second) {
                contract.symbol_map.push_back({symbol.name, symbol.name});
            }
            for (const H::Sort& parameter : symbol.domain) {
                addSortAndComponents(parameter, contract.sort_map);
            }
            addSortAndComponents(symbol.codomain, contract.sort_map);
        }
        for (const SymbolPatternRange& range : contract.source_signature.symbol_ranges) {
            contract.symbol_range_map.push_back(
                {range.prefix, range.prefix, range.first, range.first, range.count, range.suffix, range.suffix});
            addSortAndComponents(range.codomain, contract.sort_map);
        }
    }
    std::size_t observable_count = 0;
    for (const H::FunDecl& declaration : model.funs) {
        observable_count += !declaration.auxiliary || !auxiliaries_are_target_only;
    }
    const auto compact_bounds = [&](const H::VarDecl& declaration) {
        return model.packed_linear_rows
            && (declaration.sort.kind == H::SortKind::INT
                || declaration.sort.kind == H::SortKind::REAL)
            && compactNumericBound(declaration.lower_bound, declaration.sort)
            && compactNumericBound(declaration.upper_bound, declaration.sort);
    };
    std::size_t bound_count = 0, compact_bound_count = 0;
    for (const H::VarDecl& declaration : model.decls) {
        observable_count += !declaration.auxiliary || !auxiliaries_are_target_only;
        if (declaration.lower_bound || declaration.upper_bound) {
            if (compact_bounds(declaration)) { ++compact_bound_count; }
            else { ++bound_count; }
        }
    }
    if (direct_observables) {
        contract.projection.observables.reserve(
            contract.projection.observables.size() + observable_count);
    }
    contract.target_axioms.reserve(contract.target_axioms.size() + bound_count);
    contract.target_declaration_bounds.reserve(
        contract.target_declaration_bounds.size() + compact_bound_count);
    // Source adapters append bound axioms in declaration order. Consume a
    // single hint cursor so this remains linear for large finite models; a
    // malformed or out-of-order hint only loses reuse, never an obligation.
    std::size_t next_bound_hint = 0;
    for (const H::VarDecl& declaration : model.decls) {
        if (direct_observables
            && (!declaration.auxiliary || !auxiliaries_are_target_only)) {
            contract.projection.observables.push_back(
                {declaration.name, declaration.name, ProjectionKind::DIRECT});
        }
        if (!declaration.lower_bound && !declaration.upper_bound) { continue; }
        if (compact_bounds(declaration)) {
            const std::size_t index = &declaration - model.decls.data();
            // signatureOf and a validated post-pass hint preserve declaration
            // order at the start of the target signature, including auxiliaries.
            const auto& symbol = contract.target_signature.symbols[index];
            if (symbol.name != declaration.name
                || !H::sameSort(symbol.codomain, declaration.sort)) {
                throw std::logic_error("compact declaration bound lost its target symbol");
            }
            contract.target_declaration_bounds.push_back(
                {index, declaration.name, declaration.lower_bound,
                 declaration.upper_bound, declaration.loc});
            continue;
        }
        // The preceding source contract may already own this exact immutable
        // axiom. Reuse only a structurally exact post-pass match: source
        // locations and bound-expression identities are part of the check.
        const auto matches_bound_axiom = [&](const H::ExprPtr& hint) {
            if (!hint || hint->kind != H::ExprKind::OP
                || hint->loc.file != declaration.loc.file
                || hint->loc.line != declaration.loc.line
                || hint->loc.column != declaration.loc.column) {
                return false;
            }
            const bool interval = declaration.lower_bound && declaration.upper_bound;
            const H::Op expected_op = interval ? H::Op::LE
                : declaration.lower_bound ? H::Op::GE : H::Op::LE;
            const std::size_t expected_arity = interval ? 3 : 2;
            if (hint->op != expected_op || hint->args.size() != expected_arity) {
                return false;
            }
            const std::size_t variable_index = interval ? 1 : 0;
            const H::ExprPtr& variable = hint->args[variable_index];
            if (!variable || variable->kind != H::ExprKind::IDENT
                || variable->name != declaration.name
                || !H::sameSort(variable->sort, declaration.sort)) {
                return false;
            }
            if (interval) {
                return hint->args[0] == declaration.lower_bound
                    && hint->args[2] == declaration.upper_bound;
            }
            return declaration.lower_bound
                ? hint->args[1] == declaration.lower_bound
                : hint->args[1] == declaration.upper_bound;
        };
        bool reused = false;
        while (next_bound_hint < bound_axiom_hints.size()) {
            const H::ExprPtr& hint = bound_axiom_hints[next_bound_hint++];
            if (matches_bound_axiom(hint)) {
                contract.target_axioms.push_back(hint);
                reused = true;
                break;
            }
        }
        if (reused) { continue; }
        // The enclosing axiom carries the declaration's source location.
        // A paired bound is one ordered chain, avoiding two full Boolean nodes
        // (and duplicate source paths) per variable in large finite models.
        H::ExprPtr variable;
        const std::size_t index = &declaration - model.decls.data();
        if (index < declaration_terms.size()) {
            const auto& hint = declaration_terms[index];
            if (hint && hint->kind == H::ExprKind::IDENT
                && hint->name == declaration.name
                && H::sameSort(hint->sort, declaration.sort)) {
                variable = hint;
            }
        }
        if (!variable) { variable = H::mkIdent(declaration.name, declaration.sort); }
        if (declaration.lower_bound && declaration.upper_bound) {
            contract.target_axioms.push_back(H::mkOp(
                H::Op::LE, {declaration.lower_bound, variable, declaration.upper_bound},
                declaration.loc));
            continue;
        }
        if (declaration.lower_bound) {
            contract.target_axioms.push_back(
                H::mkOp(H::Op::GE, {variable, declaration.lower_bound}, declaration.loc));
        }
        if (declaration.upper_bound) {
            contract.target_axioms.push_back(
                H::mkOp(H::Op::LE, {variable, declaration.upper_bound}, declaration.loc));
        }
    }
    if (direct_observables) {
        for (const H::BoolVarRange& range : model.bool_var_ranges) {
            if (range.count != 0) {
                contract.projection.observable_ranges.push_back(
                    {range.prefix, range.prefix, range.first, range.first, range.count,
                     ProjectionKind::DIRECT});
            }
        }
    }
    for (const auto& range : model.scalar_var_ranges) {
        if (range.lower_bound || range.upper_bound) {
            contract.target_range_axioms.push_back(range);
        }
        if (direct_observables && range.count != 0) {
            contract.projection.observable_ranges.push_back(
                {range.prefix, range.prefix, range.first, range.first, range.count,
                 ProjectionKind::DIRECT, range.suffix, range.suffix});
        }
    }
    if (direct_observables) {
        for (const H::FunDecl& declaration : model.funs) {
            if (!declaration.auxiliary || !auxiliaries_are_target_only) {
                contract.projection.observables.push_back(
                    {declaration.name, declaration.name, ProjectionKind::DIRECT});
            }
        }
    }
}

std::vector<ProofObligation> standardObligations(bool optimized,
                                                 const std::string& basis) {
    std::vector<ProofObligation> result = {
        {ProofObligationKind::SOUNDNESS, EvidenceKind::TESTED,
         basis + "; regression tests exercise target models through the declared beta projection"},
        {ProofObligationKind::COMPLETENESS, EvidenceKind::TESTED,
         basis + "; regression tests cover existential auxiliary extensions without claiming a proof"},
        {ProofObligationKind::OBSERVABLES, EvidenceKind::TESTED,
         "the declared beta projection reconstructs source observables and omits auxiliary symbols"},
    };
    if (optimized) {
        result.push_back(
            {ProofObligationKind::OBJECTIVE, EvidenceKind::BY_CONSTRUCTION,
             "the objective term and direction are unchanged, so the value map is identity "
             "and preserves and reflects the source order"});
    }
    return result;
}

void addObjectiveDirections(const H::ConstraintModel& model,
                            ObjectiveMapping& mapping) {
    const std::size_t soft_count = H::softObjectiveGroups(model).size();
    for (std::size_t i = 0; i < soft_count; ++i) {
        mapping.source_directions.push_back(H::ObjKind::MINIMIZE);
        mapping.target_directions.push_back(H::ObjKind::MINIMIZE);
    }
    for (const H::Objective& objective : model.objectives) {
        mapping.source_directions.push_back(objective.kind);
        mapping.target_directions.push_back(objective.kind);
    }
}

TranslationContract sourceToRelationalContract(
    const H::ConstraintModel& model, Institution source, std::string id,
    const Fidelity& frontend_fidelity, ModelProjection projection,
    bool replace_projection, const std::string& semantic_basis,
    bool direct_source_symbols = true,
    const std::vector<H::ExprPtr>& declaration_terms = {}) {
    TranslationContract contract;
    contract.id = std::move(id);
    contract.sentence_translation_id = contract.id + ":alpha";
    contract.source = std::move(source);
    contract.target = relationalInstitution();
    // A source adapter may supply a much smaller beta map. Do not construct
    // and then discard an identity observable for every generated coordinate.
    addDirectSymbolsAndObservables(model, contract, true, !replace_projection,
                                   direct_source_symbols, declaration_terms);
    if (replace_projection) {
        contract.projection = std::move(projection);
    }
    contract.decision = sourceDecision(contract.source.id, model);
    contract.objectives.source = objectiveOrderOf(model);
    contract.objectives.target = objectiveOrderOf(model);
    addObjectiveDirections(model, contract.objectives);
    contract.objectives.value_map_id = "identity";
    contract.claimed_fidelity = frontend_fidelity;
    contract.obligations = standardObligations(hasOptimization(model), semantic_basis);
    return contract;
}

} // namespace

SourceSemanticSpec sourceSemanticSpec(const std::string& language_id) {
    SourceSemanticSpec spec;
    if (language_id == "minizinc") {
        spec.institution = miniZincInstitution();
        spec.decisions = {DecisionKind::SATISFIABILITY, DecisionKind::OPTIMIZATION};
    } else if (language_id == "flatzinc") {
        spec.institution = flatZincInstitution();
        spec.decisions = {DecisionKind::SATISFIABILITY, DecisionKind::OPTIMIZATION};
    } else if (language_id == "essence") {
        spec.institution = essencePrimeInstitution();
        spec.decisions = {DecisionKind::SATISFIABILITY, DecisionKind::OPTIMIZATION};
    } else if (language_id == "xcsp3") {
        spec.institution = xcsp3Institution();
        spec.decisions = {DecisionKind::SATISFIABILITY, DecisionKind::OPTIMIZATION};
    } else if (language_id == "hddl") {
        spec.institution = hddlInstitution();
        spec.decisions = {DecisionKind::PLAN_EXISTENCE, DecisionKind::OPTIMIZATION};
        spec.smt_embedding = SmtEmbeddingKind::BOUNDED_UNDER_APPROXIMATION;
        spec.required_bounds = {Fidelity::Bound::PLAN_HORIZON,
                                Fidelity::Bound::DECOMPOSITION_DEPTH};
        spec.rationale =
            "a bounded SMT witness is a real hierarchical plan only when both the "
            "primitive plan horizon and method-decomposition depth are explicit";
        return spec;
    } else if (language_id == "sygus") {
        spec.institution = sygusInstitution();
        spec.decisions = {DecisionKind::FUNCTION_SYNTHESIS};
        spec.smt_embedding = SmtEmbeddingKind::DIRECT_REDUCTION;
        spec.required_bounds = {Fidelity::Bound::GRAMMAR_RESTRICTION};
        spec.rationale =
            "bounded grammar search reduces to quantified SMT and preserves found "
            "functions, but incomplete encodings must record their depth restriction; "
            "an exact inductive AST encoding ranges over every finite derivation";
        return spec;
    } else if (language_id == "syntcomp") {
        spec.institution = syntcompInstitution();
        spec.decisions = {DecisionKind::REACTIVE_REALIZABILITY};
        spec.smt_embedding = SmtEmbeddingKind::DIRECT_REDUCTION;
        spec.rationale =
            "the accepted TLSF invariant fragment has a complete finite Mealy/Moore "
            "truth-table strategy space; general LTL/LTLf and AIGER/HOA games still "
            "require automata or fixpoint adapters and are refused by the frontend";
        return spec;
    } else {
        spec.institution = directSourceInstitution(language_id);
    }

    if (spec.institution.id.empty()) { return {}; }

    spec.smt_embedding = SmtEmbeddingKind::DIRECT_REDUCTION;
    spec.rationale =
        "every accepted construct has a first-order relational reduction with explicit "
        "model projection and result mapping";

    if (language_id == "wcnf" || language_id == "opb"
        || language_id == "lp" || language_id == "mps") {
        spec.decisions = {DecisionKind::SATISFIABILITY,
                          DecisionKind::OPTIMIZATION};
    } else if (language_id == "qcir" || language_id == "qdimacs") {
        spec.decisions = {DecisionKind::QBF_TRUTH};
    } else if (language_id == "aiger" || language_id == "btor2"
               || language_id == "vmt") {
        spec.decisions = {DecisionKind::SAFETY};
        spec.smt_embedding = SmtEmbeddingKind::BOUNDED_UNDER_APPROXIMATION;
        spec.required_bounds = {Fidelity::Bound::BMC_DEPTH};
        spec.rationale =
            "a bounded target model is a real counterexample trace, while bounded UNSAT "
            "does not establish global safety";
    } else if (language_id == "moxi") {
        spec.decisions = {DecisionKind::REACHABILITY};
        spec.smt_embedding = SmtEmbeddingKind::BOUNDED_UNDER_APPROXIMATION;
        spec.required_bounds = {Fidelity::Bound::BMC_DEPTH};
        spec.rationale =
            "a bounded target model is a real reachability trace, while bounded UNSAT "
            "does not establish global unreachability";
    } else if (language_id == "boogie" || language_id == "cryptoline") {
        spec.decisions = {DecisionKind::PROGRAM_VERIFICATION};
    } else if (language_id == "chc") {
        spec.decisions = {DecisionKind::HORN_SATISFIABILITY};
    } else if (language_id == "tptp") {
        spec.decisions = {DecisionKind::SATISFIABILITY, DecisionKind::VALIDITY};
        spec.smt_embedding = SmtEmbeddingKind::DIRECT_REDUCTION;
        spec.rationale =
            "CNF/FOF/TFF/TXF use their audited first-order reductions; the explicitly "
            "supported monomorphic THF0 fragment uses the strong type-code Henkin "
            "reduction. Unsupported polymorphism, include, arithmetic and other THF "
            "constructs are refused rather than erased.";
    } else if (language_id == "pddl") {
        spec.decisions = {DecisionKind::PLAN_EXISTENCE, DecisionKind::OPTIMIZATION,
                          DecisionKind::REACTIVE_REALIZABILITY};
        spec.smt_embedding = SmtEmbeddingKind::BOUNDED_UNDER_APPROXIMATION;
        spec.decision_bounds = {
            {DecisionKind::PLAN_EXISTENCE, {Fidelity::Bound::PLAN_HORIZON}},
            {DecisionKind::OPTIMIZATION, {Fidelity::Bound::PLAN_HORIZON}},
            {DecisionKind::REACTIVE_REALIZABILITY, {Fidelity::Bound::STRATEGY_SIZE}},
        };
        spec.rationale =
            "deterministic traces require a plan horizon; FOND policies require a "
            "policy-state bound and explicit outcome fairness. Bounded UNSAT does "
            "not establish unbounded absence of a plan or policy";
    }
    if (spec.decisions.empty()) {
        spec.decisions = language_id == "smtlib2"
                             ? std::vector<DecisionKind>{DecisionKind::SATISFIABILITY,
                                                         DecisionKind::OPTIMIZATION}
                             : std::vector<DecisionKind>{DecisionKind::SATISFIABILITY};
    }
    return spec;
}

bool SourceSemanticSpec::supports(DecisionKind decision) const noexcept {
    for (const DecisionKind candidate : decisions) {
        if (candidate == decision) { return true; }
    }
    return false;
}

TranslationContract miniZincToRelationalContract(const H::ConstraintModel& model) {
    TranslationContract contract;
    contract.id = "minizinc-to-typed-relational-core-v1";
    contract.sentence_translation_id =
        "minizinc-elaboration-to-typed-relational-sentences-v1";
    contract.source = miniZincInstitution();
    contract.target = relationalInstitution();
    addDirectSymbolsAndObservables(model, contract, true);
    contract.decision = sourceDecision(contract.source.id, model);
    contract.objectives.source = objectiveOrderOf(model);
    contract.objectives.target = objectiveOrderOf(model);
    addObjectiveDirections(model, contract.objectives);
    contract.objectives.value_map_id = "identity";
    contract.obligations = standardObligations(
        hasOptimization(model),
        "partial operations are represented as (defined,value) and closed at Boolean scopes");
    return contract;
}

TranslationContract flatZincToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection) {
    return sourceToRelationalContract(
        model, flatZincInstitution(), "flatzinc-to-typed-relational-core-v1",
        frontend_fidelity, std::move(projection), true,
        "FlatZinc builtins are translated as typed relations; division and element "
        "constraints include their definition domains, and output annotations define beta");
}

TranslationContract essencePrimeToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection) {
    return sourceToRelationalContract(
        model, essencePrimeInstitution(), "essence-prime-to-typed-relational-core-v1",
        frontend_fidelity, std::move(projection), true,
        "parameters and finite quantifiers are elaborated before translation; "
        "definedness closes at the nearest source Boolean expression");
}

TranslationContract xcsp3ToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    const std::vector<H::ExprPtr>& declaration_terms) {
    return sourceToRelationalContract(
        model, xcsp3Institution(), "xcsp3-to-typed-relational-core-v1",
        frontend_fidelity, {}, false,
        "XCSP3 domains and relations are materialized exactly; intension partial "
        "operators carry definition guards to their enclosing constraint",
        true, declaration_terms);
}

TranslationContract directLanguageToRelationalContract(
    const H::ConstraintModel& model, std::string language_id,
    const Fidelity& frontend_fidelity) {
    const std::string basis =
        "the frontend materializes every accepted source declaration, constraint, "
        "quantifier and objective in typed HIR and rejects unsupported constructs";
    std::string contract_id = language_id + "-to-typed-relational-core-v1";
    return sourceToRelationalContract(
        model, directSourceInstitution(language_id), std::move(contract_id),
        frontend_fidelity, {}, false, basis);
}

TranslationContract cryptoLineToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection) {
    return sourceToRelationalContract(
        model, directSourceInstitution("cryptoline"),
        "cryptoline-to-typed-relational-core-v2", frontend_fidelity,
        std::move(projection), true,
        "typed machine instructions are encoded as exact SSA relations; every safety, "
        "assertion and postcondition failure is checked under its source prefix, and "
        "beta projects generated SSA versions back to final source variables");
}

TranslationContract chcToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity) {
    return sourceToRelationalContract(
        model, directSourceInstitution("chc"),
        "chc-to-typed-relational-core-v2", frontend_fidelity, {}, false,
        "CHC-COMP commands and clause normal form are checked before lifting; alpha "
        "keeps each universal clause and relation declaration unchanged, while beta "
        "maps target function interpretations to the declared source relations");
}

TranslationContract tptpToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    bool has_positive_conjecture, Signature source_signature,
    std::vector<SymbolMapping> symbol_map,
    std::vector<Sentence> target_axioms) {
    TranslationContract contract = sourceToRelationalContract(
        model, directSourceInstitution("tptp"),
        "tptp-to-typed-relational-core-v2", frontend_fidelity, {}, false,
        "TPTP 9.3 classical formula roles are elaborated explicitly, only CNF free "
        "variables are universally closed, arity-overloaded symbols are mapped "
        "injectively, and untyped terms share one nonempty first-order universe");
    if (!signatureIsEmpty(source_signature) || !symbol_map.empty()) {
        contract.source_signature = SignatureSnapshot(std::move(source_signature));
        contract.symbol_map = std::move(symbol_map);
        contract.projection.observables.clear();
        for (const SymbolMapping& mapping : contract.symbol_map) {
            contract.projection.observables.push_back(
                {mapping.source, mapping.target, ProjectionKind::DIRECT});
        }
    }
    contract.target_axioms.insert(contract.target_axioms.end(),
                                  target_axioms.begin(), target_axioms.end());
    if (has_positive_conjecture) {
        contract.decision.source = DecisionKind::VALIDITY;
        contract.decision.polarity = VerdictPolarity::INVERT;
        contract.decision.target_sat_meaning =
            "the axioms plus negated conjecture have a model (TPTP CounterSatisfiable)";
        contract.decision.target_unsat_meaning =
            "the conjecture follows by classical refutation (a positive validity result)";
    }
    return contract;
}

TranslationContract tptpThfToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    bool has_positive_conjecture) {
    TranslationContract contract = sourceToRelationalContract(
        model, directSourceInstitution("tptp"),
        "tptp-thf0-strong-henkin-to-relational-v1", frontend_fidelity,
        ModelProjection{}, true, "the type-code strong axiom encodes every source "
        "simple type, typed application, pointwise lambda, extensional function "
        "equality, logical constant, I/K/S combinator, and choice operator. The "
        "Hahn-Richter soundness/completeness result identifies this first-order "
        "satisfiability problem with the input's Henkin semantics. This stage "
        "claims decision preservation only; it does not export a source-model beta map.",
        false);
    if (has_positive_conjecture) {
        contract.decision.source = DecisionKind::VALIDITY;
        contract.decision.target = DecisionKind::SATISFIABILITY;
        contract.decision.polarity = VerdictPolarity::INVERT;
        contract.decision.target_sat_meaning =
            "the Henkin axioms and all non-conjectures have a model falsifying at least one positive conjecture (CounterSatisfiable)";
        contract.decision.target_unsat_meaning =
            "the axioms Henkin-entail every positive conjecture (Theorem)";
    } else {
        contract.decision.source = DecisionKind::SATISFIABILITY;
        contract.decision.target = DecisionKind::SATISFIABILITY;
        contract.decision.polarity = VerdictPolarity::PRESERVE;
        contract.decision.target_sat_meaning =
            "the THF0 formulas have a Henkin model";
        contract.decision.target_unsat_meaning =
            "the THF0 formulas have no Henkin model";
    }
    return contract;
}

TranslationContract pddlToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection, Signature source_signature,
    std::vector<SymbolMapping> symbol_map,
    std::vector<Sentence> target_axioms, const std::string& policy_mode) {
    TranslationContract contract = sourceToRelationalContract(
        model, directSourceInstitution("pddl"),
        "pddl-to-typed-relational-core-v2", frontend_fidelity,
        std::move(projection), true,
        "finite grounding preserves typed ADL conditions, strict numeric definedness, "
        "simultaneous old-state effects and frames; derived predicates use their least "
        "fixed point. For discrete temporal models, rational endpoints, occurrence-specific "
        "history, interval conditions, mandatory timed facts and endpoint interference "
        "define the bounded timed trace. One-hot/noop axioms represent a bounded action "
        "prefix and beta removes padding choices to recover its source actions; "
        "numeric metrics and stable-goal makespan retain their source values",
        signatureIsEmpty(source_signature) && symbol_map.empty());
    if (!signatureIsEmpty(source_signature) || !symbol_map.empty()) {
        contract.source_signature = SignatureSnapshot(std::move(source_signature));
        contract.symbol_map = std::move(symbol_map);
        contract.sort_map.clear();
        // Object values are observable integer codes, alongside Boolean
        // definedness and real-valued state/trajectory coordinates. Derive
        // all identity sort mappings from the actual source signature.
        for (const Symbol& symbol : contract.source_signature.symbols) {
            for (const H::Sort& sort : symbol.domain) {
                addSortAndComponents(sort, contract.sort_map);
            }
            addSortAndComponents(symbol.codomain, contract.sort_map);
        }
    }
    contract.target_axioms.insert(contract.target_axioms.end(),
                                  target_axioms.begin(), target_axioms.end());
    if (!policy_mode.empty()) {
        contract.id = "pddl-fond-to-typed-relational-core-v1";
        contract.sentence_translation_id = contract.id + ":alpha";
        contract.decision.source = DecisionKind::REACTIVE_REALIZABILITY;
        contract.decision.target_sat_meaning = "a " + policy_mode
            + " source policy exists within the recorded policy-state bound";
        contract.decision.target_unsat_meaning =
            "no policy exists within the recorded state bound; larger policies remain possible";
        contract.obligations = standardObligations(false,
            "distinct active nodes represent full source states; each chosen action "
            "is applicable and all its outcomes remain in the active graph. "
            + (policy_mode == "strong"
               ? std::string("Every outcome strictly decreases a nonnegative rank, so every execution terminates at a goal")
               : std::string("Every nongoal node has a rank-decreasing outcome, so every fair execution reaches a goal; fairness requires each outcome of an infinitely repeated state/action to occur infinitely often")));
    }
    return contract;
}

TranslationContract hddlToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection, Signature source_signature,
    std::vector<SymbolMapping> symbol_map,
    std::vector<Sentence> target_axioms) {
    TranslationContract contract = sourceToRelationalContract(
        model, hddlInstitution(),
        "hddl-to-typed-relational-core-v1", frontend_fidelity,
        std::move(projection), true,
        "bounded method expansion preserves task-network order and produces only "
        "primitive frontiers executable under the shared classical successor-state "
        "semantics. Method conditions/effects execute as prefix events before their "
        "subtasks; beta separates these method events from primitive actions and "
        "removes administrative noops",
        signatureIsEmpty(source_signature) && symbol_map.empty());
    if (!signatureIsEmpty(source_signature) || !symbol_map.empty()) {
        contract.source_signature = SignatureSnapshot(std::move(source_signature));
        contract.symbol_map = std::move(symbol_map);
        contract.sort_map.clear();
        contract.sort_map.push_back({H::Sort::boolean(), H::Sort::boolean()});
        contract.sort_map.push_back({H::Sort::real(), H::Sort::real()});
    }
    contract.target_axioms.insert(contract.target_axioms.end(),
                                  target_axioms.begin(), target_axioms.end());
    return contract;
}

TranslationContract sygusToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection, Signature source_signature,
    std::vector<SymbolMapping> symbol_map,
    std::vector<Sentence> target_axioms) {
    const bool grammar_depth_restricted = std::any_of(
        frontend_fidelity.bounds.begin(), frontend_fidelity.bounds.end(),
        [](const Fidelity::Bound& bound) {
            return bound.kind == Fidelity::Bound::GRAMMAR_RESTRICTION;
        });
    const std::string semantic_basis = grammar_depth_restricted
        ? "finite grammar enumeration restricts the target function graph to one "
          "derivable candidate; universal source variables remain quantified, and beta "
          "returns the selected source define-fun witness"
        : "an inductive AST ranges over every finite derivation of the declared grammar; "
          "structurally recursive evaluation enforces every universal source constraint, "
          "and beta returns the selected source define-fun witness";
    TranslationContract contract = sourceToRelationalContract(
        model, sygusInstitution(),
        "sygus-to-typed-relational-core-v1", frontend_fidelity,
        std::move(projection), true, semantic_basis);
    if (grammar_depth_restricted) {
        contract.decision.target_unsat_meaning =
            "no definition exists within the recorded grammar-depth restriction";
    } else {
        contract.decision.target_unsat_meaning =
            "no definition derivable from the full declared grammar satisfies the "
            "universally closed source constraints";
    }
    if (!signatureIsEmpty(source_signature) || !symbol_map.empty()) {
        contract.source_signature = SignatureSnapshot(std::move(source_signature));
        contract.symbol_map = std::move(symbol_map);
        contract.sort_map.clear();
        for (const Symbol& symbol : contract.source_signature.symbols) {
            for (const H::Sort& sort : symbol.domain) {
                if (std::find_if(contract.sort_map.begin(), contract.sort_map.end(),
                                 [&](const SortMapping& mapping) {
                                     return H::sameSort(mapping.source, sort);
                                 }) == contract.sort_map.end()) {
                    contract.sort_map.push_back({sort, sort});
                }
            }
            if (std::find_if(contract.sort_map.begin(), contract.sort_map.end(),
                             [&](const SortMapping& mapping) {
                                 return H::sameSort(mapping.source, symbol.codomain);
                             }) == contract.sort_map.end()) {
                contract.sort_map.push_back({symbol.codomain, symbol.codomain});
            }
        }
    }
    contract.target_axioms.insert(contract.target_axioms.end(),
                                  target_axioms.begin(), target_axioms.end());
    return contract;
}

TranslationContract syntcompToRelationalContract(
    const H::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection, Signature source_signature,
    std::vector<SymbolMapping> symbol_map,
    std::vector<Sentence> target_axioms) {
    TranslationContract contract = sourceToRelationalContract(
        model, syntcompInstitution(),
        "syntcomp-to-typed-relational-core-v1", frontend_fidelity,
        std::move(projection), true,
        "the stateless invariant subset uses a complete response table; the basic "
        "finite-temporal subset uses the complete reachable LTLf progression DFA and "
        "a rank-decreasing reachability-game encoding. Both are exact for the decision "
        "whether a source-causal controller exists. Finite-temporal ranks ensure "
        "termination; strategy arrays and choices are existential target witnesses. The "
        "finite-temporal encoding does not decode a concrete controller through beta");
    if (!signatureIsEmpty(source_signature) || !symbol_map.empty()) {
        contract.source_signature = SignatureSnapshot(std::move(source_signature));
        contract.symbol_map = std::move(symbol_map);
        contract.sort_map.clear();
        contract.sort_map.push_back({H::Sort::boolean(), H::Sort::boolean()});
    }
    contract.target_axioms.insert(contract.target_axioms.end(),
                                  target_axioms.begin(), target_axioms.end());
    return contract;
}

namespace {

TranslationContract relationalToSmtContractImpl(const H::ConstraintModel& model,
                                               bool optimization_target,
                                               bool direct_observables,
                                               const std::vector<H::ExprPtr>& bound_axiom_hints = {},
                                               const SignatureSnapshot* postpass_signature_hint = nullptr) {
    TranslationContract contract;
    contract.id = optimization_target ? "typed-relational-core-to-omt-v1"
                                      : "typed-relational-core-to-smt-lib-v1";
    contract.sentence_translation_id =
        "typed-relational-hir-to-smt-assertions-v1";
    contract.source = relationalInstitution();
    contract.target = smtInstitution(optimization_target);
    // Auxiliary witnesses are part of the relational-core signature at this
    // stage. They remain target symbols in SMT, although beta still projects
    // only the observables required by the preceding source adapter.
    addDirectSymbolsAndObservables(model, contract, false, direct_observables,
                                   true, {}, bound_axiom_hints,
                                   postpass_signature_hint);
    const ObjectiveOrder source_order = objectiveOrderOf(model);
    contract.decision.source = coreDecision(model);
    contract.decision.target = optimization_target
                                   ? coreDecision(model)
                                   : DecisionKind::SATISFIABILITY;
    contract.decision.target_sat_meaning =
        optimization_target
            ? "the SMT/OMT assertions are feasible and the solver may return an optimum model"
            : "the SMT assertions are satisfiable";
    contract.decision.target_unsat_meaning = "the SMT/OMT assertions are unsatisfiable";
    const bool preserves_objective =
        source_order == ObjectiveOrder::SATISFACTION || optimization_target;
    contract.objectives.source = source_order;
    contract.objectives.target =
        optimization_target ? source_order : ObjectiveOrder::SATISFACTION;
    contract.objectives.order_preserving = preserves_objective;
    contract.objectives.order_reflecting = preserves_objective;
    addObjectiveDirections(model, contract.objectives);
    if (!optimization_target) { contract.objectives.target_directions.clear(); }
    contract.objectives.value_map_id =
        preserves_objective ? "identity" : "forget-objective";
    if (!preserves_objective) {
        contract.claimed_fidelity.preserves_optimum = false;
    }
    contract.obligations = standardObligations(
        source_order != ObjectiveOrder::SATISFACTION && optimization_target,
        "definedness guards and source-specific arithmetic operators are lowered explicitly");
    return contract;
}

} // namespace

TranslationContract relationalToSmtContract(const H::ConstraintModel& model,
                                             bool optimization_target) {
    return relationalToSmtContractImpl(model, optimization_target, true);
}

TranslationContract relationalToSmtContract(
    const H::ConstraintModel& model, bool optimization_target,
    const ModelProjection& required_observables) {
    if (required_observables.observables.empty()
        && required_observables.choices.empty()
        && required_observables.grammar_choices.empty()
        && required_observables.optional_observables.empty()
        && required_observables.observable_ranges.empty()) {
        return relationalToSmtContract(model, optimization_target);
    }
    return relationalToSmtContract(model, optimization_target,
                                   required_observables, {});
}

TranslationContract relationalToSmtContract(
    const H::ConstraintModel& model, bool optimization_target,
    const ModelProjection& required_observables,
    const std::vector<H::ExprPtr>& bound_axiom_hints,
    const SignatureSnapshot* postpass_signature_hint) {
    if (required_observables.observables.empty()
        && required_observables.choices.empty()
        && required_observables.grammar_choices.empty()
        && required_observables.optional_observables.empty()
        && required_observables.observable_ranges.empty()) {
        return relationalToSmtContractImpl(model, optimization_target, true,
                                           bound_axiom_hints,
                                           postpass_signature_hint);
    }
    TranslationContract contract = relationalToSmtContractImpl(
        model, optimization_target, false, bound_axiom_hints,
        postpass_signature_hint);
    // The previous stage names the core terms its beta map needs. Preserve
    // those terms verbatim through SMT lowering, so reverse composition feeds
    // exactly the assignment keys the source adapter expects.
    std::unordered_set<std::string_view> needed;
    std::size_t needed_capacity = required_observables.observables.size()
                                + required_observables.optional_observables.size();
    std::size_t optional_capacity = required_observables.optional_observables.size();
    for (const ChoiceObservable& choice : required_observables.choices) {
        needed_capacity += choice.alternatives.size();
        for (const ChoiceAlternative& alternative : choice.alternatives) {
            needed_capacity += alternative.bindings.size();
        }
    }
    for (const GrammarChoiceObservable& grammar : required_observables.grammar_choices) {
        needed_capacity += grammar.nodes.size();
        optional_capacity += grammar.nodes.size();
        for (const GrammarChoiceNode& node : grammar.nodes) {
            for (const GrammarChoiceAlternative& alternative : node.alternatives) {
                needed_capacity += alternative.bindings.size();
                optional_capacity += alternative.bindings.size();
            }
        }
    }
    needed.reserve(needed_capacity);
    contract.projection.observables.reserve(required_observables.observables.size());
    contract.projection.optional_observables.reserve(
        contract.projection.optional_observables.size() + optional_capacity);
    const auto preserve = [&](const std::string& target) {
        // Several source observables may decode the same target coordinates
        // (e.g. primitive-action and method-event views of an HTN step).
        // Reverse composition needs each coordinate once, not duplicate
        // identity observables that make ModelProjection::project fail.
        if (needed.insert(target).second) {
            contract.projection.observables.push_back(
                {target, target, ProjectionKind::DIRECT});
        }
    };
    for (const Observable& required : required_observables.observables) {
        if (required.projection == ProjectionKind::CONSTANT) { continue; }
        preserve(required.target_name);
    }
    for (const Observable& optional : required_observables.optional_observables) {
        if (optional.projection != ProjectionKind::CONSTANT
            && needed.insert(optional.target_name).second) {
            contract.projection.optional_observables.push_back(
                {optional.target_name, optional.target_name,
                 ProjectionKind::DIRECT});
        }
    }
    for (const ChoiceObservable& choice : required_observables.choices) {
        for (const ChoiceAlternative& alternative : choice.alternatives) {
            preserve(alternative.target_name);
            for (const ChoiceAlternative::Binding& binding : alternative.bindings) {
                preserve(binding.target_name);
            }
        }
    }
    for (const ObservableRange& range : required_observables.observable_ranges) {
        const auto duplicate = std::find_if(contract.projection.observable_ranges.begin(),
            contract.projection.observable_ranges.end(), [&](const ObservableRange& prior) {
                return prior.source_prefix == range.target_prefix && prior.target_prefix == range.target_prefix
                    && prior.source_first == range.target_first && prior.target_first == range.target_first
                    && prior.count == range.count
                    && prior.source_suffix == range.target_suffix
                    && prior.target_suffix == range.target_suffix;
            });
        if (duplicate == contract.projection.observable_ranges.end())
            contract.projection.observable_ranges.push_back(
                {range.target_prefix, range.target_prefix, range.target_first, range.target_first,
                 range.count, ProjectionKind::DIRECT, range.target_suffix, range.target_suffix});
    }
    for (const GrammarChoiceObservable& grammar :
        required_observables.grammar_choices) {
        for (const GrammarChoiceNode& node : grammar.nodes) {
            if (!node.selector_target.empty()
                && needed.insert(node.selector_target).second) {
                contract.projection.optional_observables.push_back(
                    {node.selector_target, node.selector_target,
                     ProjectionKind::DIRECT});
            }
            for (const GrammarChoiceAlternative& alternative : node.alternatives) {
                for (const ChoiceAlternative::Binding& binding : alternative.bindings) {
                    if (needed.insert(binding.target_name).second) {
                        contract.projection.optional_observables.push_back(
                            {binding.target_name, binding.target_name,
                             ProjectionKind::DIRECT});
                    }
                }
            }
        }
    }
    return contract;
}

bool extendRelationalWithDefinedHelpers(const H::ConstraintModel& model,
                                       const std::string& pass_pipeline,
                                       TranslationPipeline& pipeline,
                                       Diagnostics& diagnostics) {
    // This checks the signature extension, not the semantics of arbitrary
    // pass rewrites. Existing-body/constraint changes remain obligations of
    // the actual passes and their recorded fidelity and semantic tests.
    if (pipeline.stages().empty()) { return true; }
    const auto& previous = pipeline.stages().back();
    if (signatureMatchesModel(previous.target_signature, model)) { return true; }
    SignatureSnapshot after(signatureOf(model));
    if (sameSignature(previous.target_signature, after)) { return true; }
    const auto reject = [&](const std::string& reason) {
        diagnostics.error(ErrorCode::E_INTERNAL,
            "relational helper extension rejected: " + reason);
        return false;
    };
    if (pass_pipeline.empty()
        || !sameInstitutionDefinition(previous.target, relationalInstitution())) {
        return reject("the preceding institution and actual pass pipeline must be known");
    }
    const auto before_index = indexSymbols(previous.target_signature);
    std::unordered_set<std::string> canonical_names;
    for (const auto& symbol : previous.target_signature.symbols) {
        canonical_names.insert(canonicalSmtSymbol(symbol.name));
    }
    std::unordered_set<std::string> added_names;
    std::vector<const H::FunDecl*> added;
    for (const auto& function : model.funs) {
        if (!lookup(before_index, function.name).empty()) { continue; }
        if (!function.auxiliary || !function.body || !function.recursive_group.empty()) {
            return reject("new function '" + function.name
                + "' must be an auxiliary, nonrecursive definition with a body");
        }
        const auto canonical = canonicalSmtSymbol(function.name);
        if (!canonical_names.insert(canonical).second
            || !added_names.insert(function.name).second) {
            return reject("new function '" + function.name + "' is not fresh");
        }
        for (const auto& range : model.bool_var_ranges) {
            if (range.contains(canonical)) {
                return reject("new helper overlaps a compact source symbol range");
            }
        }
        for (const auto& range : model.scalar_var_ranges) {
            if (range.contains(canonical)) {
                return reject("new helper overlaps a compact source symbol range");
            }
        }
        added.push_back(&function);
    }
    Signature retained = after.materialize();
    retained.symbols.erase(std::remove_if(retained.symbols.begin(), retained.symbols.end(),
        [&](const Symbol& symbol) { return added_names.count(symbol.name) != 0; }),
        retained.symbols.end());
    if (added.empty() || !sameSignature(previous.target_signature,
                                        SignatureSnapshot(std::move(retained)))) {
        return reject("the signature delta contains more than fresh helper definitions");
    }
    // This checks bodies in their real parameter scope, including dependency
    // SCCs. Since every new definition has an empty recursive_group, a cycle
    // involving a new helper is rejected even when it passes through an old
    // function. Existing explicit recursive groups remain valid.
    if (!H::typeCheck(model, diagnostics)) { return false; }

    auto extension = relationalToSmtContract(model, hasOptimization(model),
        previous.projection, previous.target_axioms, &after);
    if (extension.decision.source != previous.decision.target
        || extension.objectives.source != previous.objectives.target
        || extension.objectives.source_directions != previous.objectives.target_directions) {
        return reject("a defined-helper extension cannot change the decision or objective order");
    }
    extension.id = "typed-relational-core-defined-helper-extension-v1";
    extension.sentence_translation_id = pass_pipeline + ":defined-helper-equations-v1";
    extension.source = previous.target;
    extension.target = previous.target;
    extension.source_signature = previous.target_signature;
    extension.target_signature = after;
    extension.decision.target = extension.decision.source;
    extension.decision.target_sat_meaning = "a source core assignment extends to the defined helpers";
    extension.decision.target_unsat_meaning = "no source core assignment satisfies the rewritten model";
    extension.objectives.target = extension.objectives.source;
    extension.objectives.target_directions = extension.objectives.source_directions;
    extension.symbol_map.erase(std::remove_if(extension.symbol_map.begin(), extension.symbol_map.end(),
        [&](const SymbolMapping& mapping) { return added_names.count(mapping.source) != 0; }),
        extension.symbol_map.end());
    extension.projection.observables.erase(std::remove_if(
        extension.projection.observables.begin(), extension.projection.observables.end(),
        [&](const Observable& observable) { return added_names.count(observable.source_name) != 0; }),
        extension.projection.observables.end());
    // Retain only axioms already established at the source-core boundary;
    // this stage adds definitions, not newly inferred post-pass bounds.
    extension.target_axioms = previous.target_axioms;
    extension.target_declaration_bounds = previous.target_declaration_bounds;
    std::size_t next_equation_binder = 0;
    for (const auto* function : added) {
        // Function parameters may legally share a spelling with a free global
        // IDENT. A quantified axiom must rename that BOUND_VAR without
        // capturing the IDENT or an inner quantifier's variables.
        auto equation_binders = function->binders;
        std::unordered_map<std::string, H::ExprPtr> renamed;
        auto taken = canonical_names;
        std::unordered_set<const H::Expr*> seen;
        std::vector<H::ExprPtr> pending{function->body};
        while (!pending.empty()) {
            auto expression = std::move(pending.back()); pending.pop_back();
            if (!expression || !seen.insert(expression.get()).second) { continue; }
            for (const auto& binder : expression->binders) {
                taken.insert(canonicalSmtSymbol(binder.name));
            }
            if (expression->kind == H::ExprKind::BOUND_VAR) {
                taken.insert(canonicalSmtSymbol(expression->name));
            }
            pending.insert(pending.end(), expression->args.begin(), expression->args.end());
        }
        for (auto& binder : equation_binders) {
            if (canonical_names.count(canonicalSmtSymbol(binder.name)) == 0) { continue; }
            std::string name;
            do { name = "!somt_defeq_" + std::to_string(next_equation_binder++); }
            while (!taken.insert(name).second);
            renamed.emplace(binder.name, H::mkBoundVar(name, binder.sort, function->loc));
            binder.name = std::move(name);
        }
        H::ExprPtr body = function->body;
        if (!renamed.empty()) {
            std::unordered_map<const H::Expr*, H::ExprPtr> memo;
            std::function<H::ExprPtr(const H::ExprPtr&)> rewrite = [&](const H::ExprPtr& expression) {
                if (const auto found = memo.find(expression.get()); found != memo.end()) {
                    return found->second;
                }
                if (expression->kind == H::ExprKind::BOUND_VAR) {
                    const auto found = renamed.find(expression->name);
                    if (found != renamed.end()) { return found->second; }
                }
                auto children = expression->args;
                bool changed = false;
                for (auto& child : children) {
                    auto replacement = rewrite(child);
                    changed = changed || replacement != child;
                    child = std::move(replacement);
                }
                H::ExprPtr result = expression;
                if (changed) {
                    auto replacement = std::make_shared<H::Expr>(*expression);
                    replacement->args = std::move(children);
                    result = std::move(replacement);
                }
                memo.emplace(expression.get(), result);
                return result;
            };
            body = rewrite(body);
        }
        std::vector<H::ExprPtr> arguments;
        for (const auto& binder : equation_binders) {
            arguments.push_back(H::mkBoundVar(binder.name, binder.sort, function->loc));
        }
        auto equation = H::mkOp(H::Op::EQ,
            {H::mkApply(function->name, function->result, std::move(arguments), function->loc), body},
            function->loc);
        if (!equation_binders.empty()) {
            equation = H::mkForall(std::move(equation_binders), equation, function->loc);
        }
        extension.target_axioms.push_back(std::move(equation));
    }
    extension.obligations = standardObligations(hasOptimization(model),
        "pass pipeline '" + pass_pipeline
        + "' introduces fresh, typed acyclic definitions with explicit universal equations; "
          "beta discards only these helpers, whose values are fixed by the old interpretation; "
          "the pass rewrite is validated by its semantic tests, not proved by signature matching");
    if (!extension.validate(diagnostics)) { return false; }
    pipeline.add(std::move(extension));
    return true;
}


} // namespace SOMTParser::Uir::Sem
