#include "somtparser/frontend/parser.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation run(const std::string& source) {
    Lang::SourceUnit unit;
    unit.main_path = "direct-constant.sl";
    unit.display_name = unit.main_path;
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "sygus";
    options.profile_id = "bmc";
    options.parse.options["grammar_mode"] = "unbounded";
    return translate(unit, options);
}

void check(const std::string& source, const std::string& binding_value,
           Sem::ChoiceAlternative::Binding::Kind expected_kind,
           const std::string& expected_body) {
    std::cerr << "checking direct source: " << source << '\n';
    const Translation translated = run(source);
    if (!translated.ok()) {
        for (const auto& diagnostic : translated.diagnostics().all()) {
            std::cerr << diagnostic.message << '\n';
        }
    }
    assert(translated.ok());
    assert(translated.report().fidelity().sound);
    assert(translated.report().fidelity().complete);
    const std::string smt = translated.toSmt2();
    assert(smt.find("__somt_sygus_witness_value_0") != std::string::npos);
    assert(smt.find("__somt_sygus_render_") == std::string::npos);
    assert(smt.find("str.replace_all") == std::string::npos);
    assert(smt.find("str.from_int") == std::string::npos);

    const auto& projection = translated.semantics().stages().front().projection;
    assert(projection.choices.size() == 1);
    const auto& alternatives = projection.choices.front().alternatives;
    assert(alternatives.size() == 1 && alternatives.front().bindings.size() == 1);
    const auto& alternative = alternatives.front();
    assert(alternative.bindings.front().kind == expected_kind);
    Sem::Assignment target{{alternative.target_name, "true"},
                           {alternative.bindings.front().target_name, binding_value}};
    Sem::Assignment source_assignment;
    Diagnostics diagnostics;
    assert(translated.semantics().project(target, source_assignment, diagnostics));
    if (source_assignment.at("definition[f]") != expected_body) {
        std::cerr << "expected: " << expected_body << '\n'
                  << "actual:   " << source_assignment.at("definition[f]") << '\n';
    }
    assert(source_assignment.at("definition[f]") == expected_body);
}

} // namespace

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    check("(set-logic LIA) (synth-fun f () Int "
          "((Start Int ((Constant Int))))) (constraint (= f (- 17))) (check-synth)",
          "-17", Sem::ChoiceAlternative::Binding::Kind::INTEGER,
          "(define-fun f () Int (- 17))");
    check("(set-logic SLIA) (synth-fun f () String "
          "((Start String ((Constant String))))) (constraint (= f \"a\")) (check-synth)",
          R"SMT("left\u{5c}u0041|""quote""")SMT",
          Sem::ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE,
          R"SMT((define-fun f () String "left\u{5c}u0041|""quote"""))SMT");
    check("(set-logic BV) (synth-fun f () (_ BitVec 8) "
          "((Start (_ BitVec 8) ((Constant (_ BitVec 8)))))) "
          "(constraint (= f #xa5)) (check-synth)",
          "(_ bv165 8)", Sem::ChoiceAlternative::Binding::Kind::BITVECTOR,
          "(define-fun f () (_ BitVec 8) #b10100101)");
    std::cout << "Direct-constant grammar witness projection tests passed.\n";
}
