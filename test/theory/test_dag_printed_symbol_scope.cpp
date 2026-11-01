#include <sstream>
#include <string>

#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

using namespace SOMTParser;

namespace {

const std::string function_name = "function_with_a_long_name_for_shared_applications";

std::string repeatedCalls(const std::string& function, const std::string& argument) {
    std::string body = "(and";
    for (unsigned i = 0; i < 12; ++i) {
        body += " (>= (" + function + " " + argument + ") " + std::to_string(i) + ")";
    }
    return body + ")";
}

std::string emitAssertion(const std::string& declaration, const std::string& argument) {
    const auto parser = newParser();
    VERIFY(parser->parseStr("(set-logic ALL)\n(declare-const " + argument + " Int)\n"
        + declaration + "\n(assert " + repeatedCalls(function_name, argument) + ")\n"));
    VERIFY(parser->getAssertions().size() == 1);
    std::ostringstream out;
    dumpSMTLIB2Shared(parser->getAssertions().front(), out);
    const auto target = out.str();
    const auto reparsed = newParser();
    VERIFY(reparsed->parseStr("(set-logic ALL)\n(declare-const " + argument + " Int)\n"
        + declaration + "\n(assert " + target + ")\n"));
    return target;
}

} // namespace

int main() {
    for (const auto& hidden : {std::string("__somt_dag_0"), std::string("|__somt_dag_0|")}) {
        const auto definition = "(define-fun " + function_name + " ((" + hidden
            + " Int)) Int (+ " + hidden + " 1))";
        const auto defined = emitAssertion(definition, "a");
        const auto declared = emitAssertion("(declare-fun " + function_name + " (Int) Int)", "a");
        // A callee's formal names and body are absent from the printed call.
        // They must neither alter caller aliases nor require traversing the
        // callee's complete definition closure during each name scan.
        VERIFY(defined == declared);
        VERIFY(defined.find("(let ((__somt_dag_0 ") != std::string::npos);

        const auto with_visible_name = emitAssertion(definition, "__somt_dag_0");
        VERIFY(with_visible_name.find("(let ((__somt_dag_0 ") == std::string::npos);
        VERIFY(with_visible_name.find("(let ((") != std::string::npos);
    }

    // Recursive application metadata has the same printed-edge boundary.
    const auto recursive = "(define-fun-rec " + function_name
        + " ((__somt_dag_0 Int)) Int (ite (<= __somt_dag_0 0) 0 ("
        + function_name + " (- __somt_dag_0 1))))";
    const auto recursive_term = emitAssertion(recursive, "a");
    VERIFY(recursive_term.find("(let ((__somt_dag_0 ") != std::string::npos);

    // The *current* definition's parameters remain in scope even if unused.
    const auto parser = newParser();
    VERIFY(parser->parseStr("(set-logic ALL)\n(declare-fun " + function_name
        + " (Int) Int)\n(define-fun owner ((__somt_dag_0 Int) (a Int)) Bool "
        + repeatedCalls(function_name, "a") + ")\n"));
    const auto definition = parser->getSymbolManager()->getFun("owner");
    VERIFY(definition != nullptr);
    const auto printed_definition = dumpFuncDef(definition);
    VERIFY(printed_definition.find("(let ((") != std::string::npos);
    VERIFY(printed_definition.find("(let ((__somt_dag_0 ") == std::string::npos);
    const auto reparsed = newParser();
    VERIFY(reparsed->parseStr("(set-logic ALL)\n(declare-fun " + function_name
        + " (Int) Int)\n" + printed_definition + "\n"));
    return 0;
}
