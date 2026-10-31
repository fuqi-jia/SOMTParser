#include "somtparser/translation/semantics.h"
#include "somtparser/frontend/parser.h"

#include <algorithm>
#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser::Uir;
namespace S = SOMTParser::Uir::Sem;

int main() {
    std::cout << "======= semantic choice template bindings =======\n";

    S::ChoiceAlternative templated;
    templated.target_name = "select_template";
    templated.label = "(define-fun f () Int (ite true __hole |__hole|))";
    templated.bindings.push_back(
        {"__hole", "selected_integer", S::ChoiceAlternative::Binding::Kind::INTEGER});

    S::ChoiceAlternative fixed{"(define-fun f () Int 0)", "select_fixed"};
    S::ChoiceObservable choice;
    choice.source_name = "definition[f]";
    choice.alternatives = {templated, fixed};

    S::ModelProjection projection;
    projection.choices.push_back(choice);
    S::Assignment target{{"select_template", "true"},
                         {"select_fixed", "false"},
                         {"selected_integer", "(- 27)"}};
    S::Assignment source;
    Diagnostics diagnostics;
    VERIFY(projection.project(target, source, diagnostics));
    VERIFY(source.at("definition[f]")
           == "(define-fun f () Int (ite true (- 27) (- 27)))");
    SOMTParser::ParserPtr projected_parser = SOMTParser::newParser();
    VERIFY(projected_parser->parseStr(source.at("definition[f]")));

    target.erase("selected_integer");
    Diagnostics missing_diagnostics;
    VERIFY(!projection.project(target, source, missing_diagnostics));
    VERIFY(missing_diagnostics.size() != 0);

    target["selected_integer"] = "(+ 1 2)";
    Diagnostics mistyped_diagnostics;
    VERIFY(!projection.project(target, source, mistyped_diagnostics));
    VERIFY(mistyped_diagnostics.size() != 0);

    target["selected_integer"] = "-5";
    Diagnostics negative_diagnostics;
    VERIFY(projection.project(target, source, negative_diagnostics));
    VERIFY(source.at("definition[f]")
           == "(define-fun f () Int (ite true (- 5) (- 5)))");
    SOMTParser::ParserPtr negative_parser = SOMTParser::newParser();
    VERIFY(negative_parser->parseStr(source.at("definition[f]")));

    S::ChoiceAlternative bitvector;
    bitvector.target_name = "select_bitvector";
    bitvector.label = "(define-fun g () (_ BitVec 8) __bv_hole)";
    S::ChoiceAlternative::Binding bv_binding;
    bv_binding.placeholder = "__bv_hole";
    bv_binding.target_name = "selected_bitvector";
    bv_binding.kind = S::ChoiceAlternative::Binding::Kind::BITVECTOR;
    bv_binding.bit_width = 8;
    bitvector.bindings.push_back(bv_binding);
    S::ChoiceAlternative bitvector_other{"(define-fun g () (_ BitVec 8) #x00)",
                                         "select_bitvector_other"};
    S::ChoiceObservable bitvector_choice;
    bitvector_choice.source_name = "definition[g]";
    bitvector_choice.alternatives = {bitvector, bitvector_other};
    S::ModelProjection bitvector_projection;
    bitvector_projection.choices.push_back(bitvector_choice);
    S::Assignment bitvector_target{{"select_bitvector", "true"},
                                   {"select_bitvector_other", "false"},
                                   {"selected_bitvector", "(_ bv42 8)"}};
    S::Assignment bitvector_source;
    Diagnostics bitvector_diagnostics;
    VERIFY(bitvector_projection.project(bitvector_target, bitvector_source,
                                        bitvector_diagnostics));
    VERIFY(bitvector_source.at("definition[g]")
           == "(define-fun g () (_ BitVec 8) #b00101010)");
    SOMTParser::ParserPtr bitvector_parser = SOMTParser::newParser();
    VERIFY(bitvector_parser->parseStr(bitvector_source.at("definition[g]")));

    bitvector_target["selected_bitvector"] = "#b101010";
    Diagnostics wrong_width_diagnostics;
    VERIFY(!bitvector_projection.project(bitvector_target, bitvector_source,
                                         wrong_width_diagnostics));
    bitvector_target["selected_bitvector"] = "(_ bv256 8)";
    Diagnostics modular_literal_diagnostics;
    VERIFY(bitvector_projection.project(bitvector_target, bitvector_source,
                                        modular_literal_diagnostics));
    VERIFY(bitvector_source.at("definition[g]")
           == "(define-fun g () (_ BitVec 8) #b00000000)");

    SOMTParser::Uir::Hir::ConstraintModel empty_model;
    S::TranslationContract invalid_width_contract =
        S::relationalToSmtContract(empty_model, false);
    S::ChoiceAlternative invalid_width_alternative;
    invalid_width_alternative.target_name = "select_invalid";
    invalid_width_alternative.label = "(define-fun h () Bool true)";
    S::ChoiceAlternative::Binding invalid_width_binding;
    invalid_width_binding.placeholder = "__hole";
    invalid_width_binding.target_name = "selected_value";
    invalid_width_binding.kind = S::ChoiceAlternative::Binding::Kind::BITVECTOR;
    invalid_width_alternative.bindings.push_back(invalid_width_binding);
    S::ChoiceObservable invalid_width_choice;
    invalid_width_choice.source_name = "definition[h]";
    invalid_width_choice.alternatives.push_back(invalid_width_alternative);
    invalid_width_contract.projection.choices.push_back(invalid_width_choice);
    Diagnostics invalid_width_contract_diagnostics;
    VERIFY(!invalid_width_contract.validate(invalid_width_contract_diagnostics));
    VERIFY(std::any_of(invalid_width_contract_diagnostics.all().begin(),
                       invalid_width_contract_diagnostics.all().end(),
                       [](const Diagnostic& diagnostic) {
                           return diagnostic.message.find("invalid kind or width")
                                  != std::string::npos;
                       }));
    invalid_width_contract.projection.choices.front().alternatives.front()
        .bindings.front().kind =
        static_cast<S::ChoiceAlternative::Binding::Kind>(99);
    Diagnostics invalid_kind_contract_diagnostics;
    VERIFY(!invalid_width_contract.validate(invalid_kind_contract_diagnostics));
    VERIFY(std::any_of(invalid_kind_contract_diagnostics.all().begin(),
                       invalid_kind_contract_diagnostics.all().end(),
                       [](const Diagnostic& diagnostic) {
                           return diagnostic.message.find("invalid kind or width")
                                  != std::string::npos;
                       }));


    // SMT_TERM is a String-valued source witness. Decode its model literal
    // once, then substitute the complete source term without interpreting its
    // own String escapes a second time.
    {
        S::ChoiceAlternative alternative;
        alternative.target_name = "selected";
        alternative.label = "(define-fun reconstructed () String __term)";
        alternative.bindings.push_back({"__term", "witness",
                                        S::ChoiceAlternative::Binding::Kind::SMT_TERM});
        S::ChoiceObservable observable;
        observable.source_name = "definition[reconstructed]";
        observable.alternatives.push_back(alternative);
        S::ModelProjection projection;
        projection.choices.push_back(observable);
        S::Assignment target{{"selected", "true"}};
        S::Assignment source;
        for (const std::string& literal : {
                 R"SMT("""\u{5c}u{41}""")SMT",
                 R"SMT("""\u005cu{41}""")SMT"}) {
            target["witness"] = literal;
            Diagnostics diagnostics;
            VERIFY(projection.project(target, source, diagnostics));
            VERIFY(source.at("definition[reconstructed]")
                   == R"SMT((define-fun reconstructed () String "\u{41}"))SMT");
            auto parser = SOMTParser::newParser();
            VERIFY(parser->parseStr(source.at("definition[reconstructed]")));
        }
        // These outer Strings contain an unterminated inner source String.
        for (const std::string& literal : {R"SMT("""")SMT", R"SMT("""a""""")SMT"}) {
            target["witness"] = literal;
            Diagnostics diagnostics;
            VERIFY(!projection.project(target, source, diagnostics));
        }
    }

    // A direct String grammar root returns a String value whose model token
    // is already a legal source String expression; it must be copied as one
    // literal instead of decoded as the lexical contents of an SMT_TERM.
    {
        S::ChoiceAlternative alternative;
        alternative.target_name = "selected_string";
        alternative.label = "(define-fun reconstructed () String __string_value)";
        alternative.bindings.push_back({
            "__string_value", "string_value",
            S::ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE});
        S::ChoiceObservable observable;
        observable.source_name = "definition[direct-string]";
        observable.alternatives.push_back(alternative);
        S::ModelProjection projection;
        projection.choices.push_back(observable);
        S::Assignment target{{"selected_string", "true"},
                             {"string_value", R"SMT("left\u{5c}u{41}|""quote""")SMT"}};
        S::Assignment source;
        Diagnostics diagnostics;
        const bool projected = projection.project(target, source, diagnostics);
        if (!projected) {
            for (const auto& diagnostic : diagnostics.all()) {
                std::cerr << diagnostic.message << '\n';
            }
        }
        VERIFY(projected);
        VERIFY(source.at("definition[direct-string]")
               == R"SMT((define-fun reconstructed () String "left\u{5c}u{41}|""quote"""))SMT");
        auto parser = SOMTParser::newParser();
        VERIFY(parser->parseStr(source.at("definition[direct-string]")));
        target["string_value"] = R"SMT("unterminated)SMT";
        Diagnostics invalid_diagnostics;
        VERIFY(!projection.project(target, source, invalid_diagnostics));
    }

    std::cout << "All semantic choice binding tests passed.\n";
    return 0;
}
