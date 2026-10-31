#include "somtparser/languages/smtlib2.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

static std::size_t count(const std::string& text, const std::string& token) {
    std::size_t result = 0, at = 0;
    while ((at = text.find(token, at)) != std::string::npos) {
        ++result;
        at += token.size();
    }
    return result;
}

static Lang::ParseOutcome parse(const std::string& source) {
    Lang::SourceUnit unit;
    unit.display_name = "definitions.smt2";
    unit.inline_source = source;
    return Lang::mkSmtLib2Language()->parse(unit, Lang::ParseOptions{});
}

static std::string translate(const std::string& source) {
    Lang::SourceUnit unit;
    unit.display_name = "definitions.smt2";
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "smtlib2";
    auto result = SOMTParser::translate(unit, options);
    VERIFY(result.ok());
    return result.toSmt2();
}

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    // A deep DAG of zero-argument aliases must not become thousands of new
    // solver variables and hard equalities. Both branches reuse the same
    // predecessor, so recursively expanding the source would be exponential.
    constexpr int depth = 12000;
    std::string source = "(set-logic QF_BV)(declare-const x (_ BitVec 8))"
                         "(define-fun d0 () (_ BitVec 8) x)";
    for (int i = 1; i <= depth; ++i) {
        const auto before = "d" + std::to_string(i - 1);
        source += "(define-fun d" + std::to_string(i)
            + " () (_ BitVec 8) (bvadd " + before + " " + before + "))";
    }
    source += "(assert (= d" + std::to_string(depth) + " #x00))(check-sat)";
    {
        const auto result = parse(source);
        VERIFY(result.model && !result.diagnostics.hasErrors());
        VERIFY(result.model->funs.size() == depth + 1);
        VERIFY(result.model->constraints.size() == 1);
        for (const auto& function : result.model->funs) {
            VERIFY(function.body && function.binders.empty());
            VERIFY(function.recursive_group.empty());
        }
    }
    const auto output = translate(source);
    VERIFY(count(output, "(define-fun ") == depth + 1);
    VERIFY(count(output, "(assert ") == 1);
    VERIFY(output.find("(forall ") == std::string::npos);
    VERIFY(count(output, "(declare-fun ") == 1);
    auto reader = newParser();
    VERIFY(reader->parseStr(output));
    VERIFY(reader->getAssertions().size() == 1);

    // Bound parameters shadow globals, while ordinary UFs remain uninterpreted.
    const auto mixed = parse("(declare-const x Bool)(declare-fun u (Int) Int)"
        "(define-fun inc ((x Int)) Int (+ (u x) 1))"
        "(assert x)(assert (= (inc 2) 4))(check-sat)");
    VERIFY(mixed.model && !mixed.diagnostics.hasErrors());
    VERIFY(mixed.model->constraints.size() == 2);
    bool saw_uf = false, saw_definition = false;
    for (const auto& function : mixed.model->funs) {
        if (function.name == "u") saw_uf = !function.body;
        if (function.name == "inc") {
            saw_definition = function.body && function.binders.size() == 1;
            VERIFY(function.binders.front().name != "x");
            VERIFY(function.binders.front().sort.kind == H::SortKind::INT);
        }
    }
    VERIFY(saw_uf && saw_definition);

    // Explicit mutually recursive groups must not enter the acyclic branch.
    const std::string recursive_source = "(define-funs-rec "
        "((even ((n Int)) Bool) (odd ((n Int)) Bool)) "
        "((ite (= n 0) true (odd (- n 1)))"
        " (ite (= n 0) false (even (- n 1)))))"
        "(assert (even 4))(check-sat)";
    const auto recursive = parse(recursive_source);
    VERIFY(recursive.model && !recursive.diagnostics.hasErrors());
    VERIFY(recursive.model->funs.size() == 2);
    const auto& group = recursive.model->funs.front().recursive_group;
    VERIFY(!group.empty());
    for (const auto& function : recursive.model->funs) {
        VERIFY(function.body && function.recursive_group == group);
    }
    const auto recursive_output = translate(recursive_source);
    VERIFY(count(recursive_output, "(define-funs-rec ") == 1);
    auto recursive_reader = newParser();
    VERIFY(recursive_reader->parseStr(recursive_output));

    // The frontend represents the final snapshot; a popped definition must
    // not be revived when source function bodies are retained.
    const auto scoped = parse("(define-fun kept () Int 2)(push 1)"
        "(define-fun removed () Int 9)(pop 1)(assert (= kept 2))(check-sat)");
    VERIFY(scoped.model && !scoped.diagnostics.hasErrors());
    VERIFY(scoped.model->funs.size() == 1);
    VERIFY(scoped.model->funs.front().name == "kept");
    VERIFY(scoped.model->funs.front().body);
}
