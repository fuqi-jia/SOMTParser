#include "somtparser/parser.h"

#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <string_view>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& text, const std::string& needle) {
    return text.find(needle) != std::string::npos;
}

std::string_view first_form_at(const std::string& text, std::size_t start) {
    const auto open = text.find('(', start);
    if (open == std::string::npos) return {};
    unsigned depth = 0;
    for (std::size_t i = open; i < text.size(); ++i) {
        if (text[i] == '(') ++depth;
        else if (text[i] == ')' && --depth == 0)
            return std::string_view(text).substr(open, i - open + 1);
    }
    return {};
}

std::uint64_t canonical_hash(const std::string& text) {
    std::uint64_t hash = 0;
    for (unsigned char byte : text) {
        hash = hash * 1099511628211ull + byte;
    }
    return hash;
}

} // namespace

int main() {
    const std::string source =
        "(set-logic ALL)\n"
        "(declare-const a Int)\n"
        "(declare-const __somt_dag_0 Int)\n"
        "(assert (and (= __somt_dag_0 __somt_dag_0)\n"
        "  (forall ((q Int))\n"
        "    (= (+ (* (+ q a) 2) (* (+ q a) 2) (* (+ q a) 2) (* (+ q a) 2)) 24))))\n";

    ParserPtr parser = newParser();
    VERIFY(parser->parseStr(source));
    const auto assertions = parser->getAssertions();
    VERIFY(assertions.size() == 1);
    const std::string canonical = dumpSMTLIB2(assertions.front());
    VERIFY(!has(canonical, "(let ((__somt_dag_"));
    VERIFY(assertions.front()->orderKey() == canonical_hash(canonical));

    std::ostringstream shared;
    dumpSMTLIB2Shared(assertions.front(), shared);
    const std::string shared_term = shared.str();
    const auto forall_pos = shared_term.find("(forall");
    const auto generated_alias_pos = shared_term.find("(let ((__somt_dag_");
    VERIFY(forall_pos != std::string::npos);
    VERIFY(generated_alias_pos != std::string::npos);
    VERIFY(generated_alias_pos > forall_pos);
    VERIFY(has(shared_term, "__somt_dag_0 __somt_dag_0"));
    VERIFY(!has(shared_term, "(let ((__somt_dag_0 "));

    // Pattern variables bind only in the corresponding match body. Sharing
    // there is safe; hoisting a let across the pattern would leave x free.
    const std::string match_source =
        "(set-logic ALL)\n"
        "(declare-datatype MaybeInt ((none) (some (value Int))))\n"
        "(declare-const m MaybeInt)\n"
        "(assert\n"
        "  (and\n"
        "    (match m ((none true) ((some x)\n"
        "      (= (+ (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2)) 8))))\n"
        "    (match m ((none true) ((some x)\n"
        "      (= (+ (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2)) 8))))))\n";
    ParserPtr match_parser = newParser();
    VERIFY(match_parser->parseStr(match_source));
    const auto match_assertions = match_parser->getAssertions();
    VERIFY(match_assertions.size() == 1);
    std::ostringstream match_shared;
    dumpSMTLIB2Shared(match_assertions.front(), match_shared);
    const std::string match_term = match_shared.str();
    const auto match_pos = match_term.find("(match");
    const auto pattern_pos = match_term.find("(some x)");
    const auto match_alias_pos = match_term.find("(let ((__somt_dag_");
    VERIFY(match_pos != std::string::npos);
    VERIFY(pattern_pos > match_pos);
    VERIFY(match_alias_pos > pattern_pos);

    ParserPtr reparsed_match = newParser();
    VERIFY(reparsed_match->parseStr(
        "(set-logic ALL)\n"
        "(declare-datatype MaybeInt ((none) (some (value Int))))\n"
        "(declare-const m MaybeInt)\n(assert " + match_term + ")\n"));

    // Function-application child[0] is definition metadata, not a printed
    // argument. The old planner walked through it and hoisted a repeated
    // function-body term containing formal x into the caller's scope.
    std::string shared_function_body = "x";
    for (unsigned i = 0; i < 18; ++i)
        shared_function_body = "(+ " + shared_function_body + " 1)";
    const std::string function_body =
        "(ite (= x 0) " + shared_function_body
        + " (ite (= x 1) " + shared_function_body + " 0))";
    const std::string function_source =
        "(set-logic ALL)\n"
        "(declare-const a Int)\n"
        "(define-fun f ((x Int)) Int " + function_body + ")\n"
        "(assert (= (+ (f a) (f (+ a 1)) (f (+ a 2)) (f (+ a 3))) 10))\n";
    ParserPtr function_parser = newParser();
    VERIFY(function_parser->parseStr(function_source));
    const auto function_assertions = function_parser->getAssertions();
    VERIFY(function_assertions.size() == 1);
    std::ostringstream function_shared;
    dumpSMTLIB2Shared(function_assertions.front(), function_shared);
    const std::string function_term = function_shared.str();
    VERIFY(!has(function_term, " x"));
    VERIFY(!has(function_term, "(let"));
    ParserPtr function_reparse = newParser();
    VERIFY(function_reparse->parseStr(
        "(set-logic ALL)\n(declare-const a Int)\n"
        "(declare-fun f (Int) Int)\n(assert " + function_term + ")\n"));

    std::string recursive_shared_body = "r";
    for (unsigned i = 0; i < 18; ++i)
        recursive_shared_body = "(+ " + recursive_shared_body + " 1)";
    const std::string recursive_body =
        "(ite (= r 0) " + recursive_shared_body
        + " (ite (= r 1) " + recursive_shared_body + " (f (- r 1))))";
    const std::string recursive_source =
        "(set-logic ALL)\n"
        "(declare-const a Int)\n"
        "(define-fun-rec f ((r Int)) Int " + recursive_body + ")\n"
        "(assert (= (+ (f a) (f (+ a 1)) (f (+ a 2)) (f (+ a 3))) 10))\n";
    ParserPtr recursive_parser = newParser();
    VERIFY(recursive_parser->parseStr(recursive_source));
    const auto recursive_assertions = recursive_parser->getAssertions();
    VERIFY(recursive_assertions.size() == 1);
    std::ostringstream recursive_shared;
    dumpSMTLIB2Shared(recursive_assertions.front(), recursive_shared);
    const std::string recursive_term = recursive_shared.str();
    VERIFY(!has(recursive_term, " r"));
    VERIFY(!has(recursive_term, "(let"));
    ParserPtr recursive_reparse = newParser();
    VERIFY(recursive_reparse->parseStr(
        "(set-logic ALL)\n(declare-const a Int)\n"
        "(declare-fun f (Int) Int)\n(assert " + recursive_term + ")\n"));

    // Regression for same-name/same-sort quantifier shadowing. mkQuantVar
    // intentionally hash-conses the outer and inner `x` nodes, so an alias
    // created in the outer body must not be visible in the inner body.
    const std::string shadow_source =
        "(set-logic ALL)\n"
        "(assert (exists ((x Int)) (and "
        "(= (+ (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2)) 0) "
        "(>= (+ (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2)) 0) "
        "(exists ((x Int)) (= (+ (* (+ x 1) 2) (* (+ x 1) 2) "
        "(* (+ x 1) 2) (* (+ x 1) 2)) 8)))))\n";
    ParserPtr shadow_parser = newParser();
    VERIFY(shadow_parser->parseStr(shadow_source));
    const auto shadow_assertions = shadow_parser->getAssertions();
    VERIFY(shadow_assertions.size() == 1);
    std::ostringstream shadow_shared;
    dumpSMTLIB2Shared(shadow_assertions.front(), shadow_shared);
    const std::string shadow_term = shadow_shared.str();
    const auto outer_alias_pos = shadow_term.find("(let ((__somt_dag_");
    const auto inner_quant_pos = shadow_term.find("(exists ((x Int))", 1);
    VERIFY(outer_alias_pos != std::string::npos);
    VERIFY(inner_quant_pos != std::string::npos);
    std::vector<std::string> outer_aliases;
    for (std::size_t pos = 0; pos < inner_quant_pos;) {
        const auto let_pos = shadow_term.find("(let ((__somt_dag_", pos);
        if (let_pos == std::string::npos || let_pos >= inner_quant_pos) break;
        const auto name_begin = let_pos + std::string("(let ((").size();
        const auto name_end = shadow_term.find(' ', name_begin);
        VERIFY(name_end != std::string::npos);
        outer_aliases.push_back(shadow_term.substr(name_begin, name_end - name_begin));
        pos = name_end;
    }
    VERIFY(!outer_aliases.empty());
    const std::string_view inner_form = first_form_at(shadow_term, inner_quant_pos);
    VERIFY(!inner_form.empty());
    for (const auto& alias : outer_aliases)
        VERIFY(inner_form.find(alias) == std::string_view::npos);
    ParserPtr shadow_reparse = newParser();
    VERIFY(shadow_reparse->parseStr("(set-logic ALL)\n(assert " + shadow_term + ")\n"));

    // The same alias boundary applies to a let body: its RHS is in the outer
    // scope, while its body sees the new binding and must plan locally.
    const std::string let_shadow_source =
        "(set-logic ALL)\n"
        "(assert (exists ((x Int)) (and "
        "(< (+ (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2)) 0) "
        "(<= (+ (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2) (* (+ x 1) 2)) 0) "
        "(let ((x (+ x 1))) (= (+ (* (+ x 1) 2) (* (+ x 1) 2) "
        "(* (+ x 1) 2) (* (+ x 1) 2)) 8)))))\n";
    ParserPtr let_shadow_parser = newParser();
    VERIFY(let_shadow_parser->parseStr(let_shadow_source));
    const auto let_shadow_assertions = let_shadow_parser->getAssertions();
    VERIFY(let_shadow_assertions.size() == 1);
    std::ostringstream let_shadow_shared;
    dumpSMTLIB2Shared(let_shadow_assertions.front(), let_shadow_shared);
    ParserPtr let_shadow_reparse = newParser();
    VERIFY(let_shadow_reparse->parseStr(
        "(set-logic ALL)\n(assert " + let_shadow_shared.str() + ")\n"));

    // Match scrutinees are ordinary terms in the enclosing scope. A repeated
    // DAG there should be compacted before the case list, while pattern-bound
    // sharing remains local to each body.
    std::string large_term = "(+ a 1)";
    for (unsigned i = 0; i < 12; ++i) large_term = "(* " + large_term + " 2)";
    std::string scrutinee_arg = "(+";
    for (unsigned i = 0; i < 8; ++i) scrutinee_arg += " " + large_term;
    scrutinee_arg += ")";
    const std::string scrutinee_source =
        "(set-logic ALL)\n"
        "(declare-datatype MaybeInt ((none) (some (value Int))))\n"
        "(declare-const a Int)\n"
        "(assert (match (some " + scrutinee_arg
            + ") ((none false) ((some x) (= x 0)))))\n";
    ParserPtr scrutinee_parser = newParser();
    VERIFY(scrutinee_parser->parseStr(scrutinee_source));
    const auto scrutinee_assertions = scrutinee_parser->getAssertions();
    VERIFY(scrutinee_assertions.size() == 1);
    std::ostringstream scrutinee_shared;
    dumpSMTLIB2Shared(scrutinee_assertions.front(), scrutinee_shared);
    const std::string scrutinee_term = scrutinee_shared.str();
    const auto scrutinee_match_pos = scrutinee_term.find("(match");
    const auto scrutinee_alias_pos = scrutinee_term.find("(let ((__somt_dag_");
    const auto scrutinee_pattern_pos = scrutinee_term.find("((some x)");
    VERIFY(scrutinee_match_pos == 0);
    VERIFY(scrutinee_alias_pos > scrutinee_match_pos);
    VERIFY(scrutinee_alias_pos < scrutinee_pattern_pos);
    ParserPtr scrutinee_reparse = newParser();
    VERIFY(scrutinee_reparse->parseStr(
        "(set-logic ALL)\n(declare-datatype MaybeInt ((none) (some (value Int))))\n"
        "(declare-const a Int)\n(assert " + scrutinee_term + ")\n"));

    std::cout << "Lexical scope printer safety tests passed.\n";
    return 0;
}
