#include "somtparser/frontend/parser.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;

namespace {

bool has(const std::string& haystack, const std::string& needle) {
    return haystack.find(needle) != std::string::npos;
}

Translation run(const std::string& path, unsigned depth) {
    Lang::SourceUnit unit;
    unit.main_path = path;
    unit.display_name = path;
    TranslateOptions options;
    options.language_id = "sygus";
    options.profile_id = "bmc";
    options.parse.options["grammar_depth"] = std::to_string(depth);
    return translate(unit, options);
}

Translation runInline(const std::string& source, unsigned depth = 1) {
    Lang::SourceUnit unit;
    unit.main_path = "compact-source-witness.sl";
    unit.display_name = unit.main_path;
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "sygus";
    options.profile_id = "bmc";
    options.parse.options["grammar_depth"] = std::to_string(depth);
    return translate(unit, options);
}

} // namespace

int main() {
    std::cout << "======= SyGuS bounded synthesis =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* language = Lang::LanguageRegistry::instance().byId("sygus");
    assert(language != nullptr);
    assert(!has(language->displayName(), "pending"));

    // The selector relation is one linear cardinality equation in both the
    // emitted script and the semantic contract, independent of candidate count.
    {
        Lang::SourceUnit unit;
        unit.main_path = "four-selectors.sl";
        unit.inline_source =
            "(set-logic LIA) "
            "(synth-fun f ((x Int)) Int ((Start Int)) ((Start Int (0 1 2 3)))) "
            "(declare-var x Int) (constraint (= (f x) (f x))) (check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "0";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        const auto& axioms = translation.semantics().stages().front().target_axioms;
        assert(axioms.size() == 1);
        assert(axioms.front()->kind == H::ExprKind::OP);
        assert(axioms.front()->op == H::Op::EQ);
        assert(axioms.front()->args.size() == 2);
        const H::ExprPtr& count = axioms.front()->args.front();
        assert(count->kind == H::ExprKind::OP);
        assert(count->op == H::Op::ADD);
        assert(count->args.size() == 4);
        for (const H::ExprPtr& term : count->args) {
            assert(term->kind == H::ExprKind::OP);
            assert(term->op == H::Op::ITE);
        }
    }

    // Every candidate is guarded by one finite derivation selector, but the
    // specification remains universally closed over declare-var symbols.
    {
        const Translation translation = run(
            "languages/sygus/instances/ok/max2.sl", 2);
        assert(translation.ok());
        const std::string smt = translation.toSmt2();
        assert(has(smt, "__somt_sygus_candidate_"));
        assert(has(smt, "(forall ((x Int) (y Int))"));
        assert(has(smt, "(ite (<= x y) y x)"));
        assert(!has(smt, "declare-fun max2"));
        ParserPtr parser = newParser();
        assert(parser->parseStr(smt));

        const auto& stages = translation.semantics().stages();
        assert(stages.size() == 2);
        assert(stages.front().id == "sygus-to-typed-relational-core-v1");
        assert(stages.front().source.id == "sygus");
        assert(stages.front().decision.source
               == Sem::DecisionKind::FUNCTION_SYNTHESIS);
        assert(!stages.front().source_signature.symbols.empty());
        assert(stages.front().source_signature.symbols.size()
               == stages.front().symbol_map.size());
        assert(!stages.front().target_axioms.empty());
        Diagnostics diagnostics;
        assert(translation.semantics().validate(diagnostics));
    }

    // beta returns a source definition, not the internal selector assignment.
    {
        const Translation translation = run(
            "languages/sygus/instances/ok/max2.sl", 2);
        assert(translation.ok());
        const Sem::ChoiceObservable& choice =
            translation.semantics().stages().front().projection.choices.front();
        Sem::Assignment target;
        bool found = false;
        for (const Sem::ChoiceAlternative& alternative : choice.alternatives) {
            const bool selected = has(alternative.label,
                                      "(ite (<= x y) y x)");
            target.emplace(alternative.target_name, selected ? "true" : "false");
            found = found || selected;
        }
        assert(found);
        Sem::Assignment source;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, source, diagnostics));
        assert(source.size() == 1);
        assert(source.at("definition[max2]")
               == "(define-fun max2 ((x Int) (y Int)) Int "
               "(ite (<= x y) y x))");
    }

    // Multiple nullary synth-funs get independent beta observables while
    // their selector equations and source specification remain joint.
    {
        Lang::SourceUnit unit;
        unit.main_path = "joint-nullary-synthesis.sl";
        unit.inline_source =
            "(set-logic LIA) "
            "(synth-fun left () Int ((Start Int)) ((Start Int (0 1)))) "
            "(synth-fun right () Int ((Start Int)) ((Start Int (0 1)))) "
            "(constraint (= (+ left right) 1)) (check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "0";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        const auto& stage = translation.semantics().stages().front();
        assert(stage.projection.choices.size() == 2);
        assert(stage.projection.choices[0].source_name == "definition[left]");
        assert(stage.projection.choices[1].source_name == "definition[right]");
        const std::string smt = translation.toSmt2();
        assert(has(smt, "__somt_sygus_candidate_0_"));
        assert(has(smt, "__somt_sygus_candidate_1_"));
        // Independent Python SAT/UNSAT tests verify the coupled relation.
        assert(has(smt, "__somt_sygus_function_0"));
        assert(has(smt, "__somt_sygus_function_1"));
        ParserPtr parsed = newParser();
        assert(parsed->parseStr(smt));

        Sem::Assignment target;
        for (const Sem::ChoiceObservable& observable : stage.projection.choices) {
            bool found_expected = false;
            const std::string expected_suffix = observable.source_name == "definition[left]"
                                                    ? " Int 0)" : " Int 1)";
            for (const Sem::ChoiceAlternative& alternative : observable.alternatives) {
                const bool selected = alternative.label.size() >= expected_suffix.size()
                    && alternative.label.compare(
                           alternative.label.size() - expected_suffix.size(),
                           expected_suffix.size(), expected_suffix) == 0;
                target.emplace(alternative.target_name, selected ? "true" : "false");
                found_expected = found_expected || selected;
            }
            assert(found_expected);
        }
        Sem::Assignment source;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, source, diagnostics));
        assert(source.size() == 2);
        assert(source.at("definition[left]") == "(define-fun left () Int 0)");
        assert(source.at("definition[right]") == "(define-fun right () Int 1)");
    }

    // Helpers that are legal in the source logic but reserved in the broader
    // target logic are alpha-renamed only in the target encoding. Local
    // parameter and let bindings with the same spelling remain bound, while
    // beta keeps the source helper name in the synthesized definition.
    {
        Lang::SourceUnit unit;
        unit.main_path = "reserved-target-helper-name.sl";
        unit.inline_source =
            "(set-logic BV) "
            "(define-fun lea ((base (BitVec 32)) (index (BitVec 32)) "
            "(scale (BitVec 32)) (disp (BitVec 32))) (BitVec 32) "
            "(bvadd base (bvadd (bvshl index scale) disp))) "
            "(define-fun load-val ((base (BitVec 32)) (index (BitVec 32)) "
            "(scale (BitVec 32)) (disp (BitVec 32)) (ptr (BitVec 32)) "
            "(mem (BitVec 32))) (BitVec 32) "
            "(ite (= ptr (lea base index scale disp)) mem #x00000000)) "
            "(define-fun store ((base (BitVec 32)) (index (BitVec 32)) "
            "(scale (BitVec 32)) (disp (BitVec 32)) (ptr (BitVec 32)) "
            "(mem (BitVec 32)) (val (BitVec 32))) (BitVec 32) "
            "(ite (= ptr (lea base index scale disp)) val #x00000000)) "
            "(define-fun formal-shadow ((store (BitVec 32))) (BitVec 32) store) "
            "(define-fun let-shadow ((x (BitVec 32))) (BitVec 32) "
            "(let ((store (BitVec 32) x)) store)) "
            "(define-fun wrapped ((base (BitVec 32)) (index (BitVec 32)) "
            "(scale (BitVec 32)) (disp (BitVec 32)) (mem (BitVec 32))) "
            "(BitVec 32) (let ((saved (BitVec 32) mem)) "
            "(store base index scale disp base mem saved))) "
            "(synth-fun f ((base (BitVec 32)) (index (BitVec 32)) "
            "(scale (BitVec 32)) (disp (BitVec 32)) (mem (BitVec 32)) "
            "(bit (BitVec 32))) (BitVec 32) "
            "((Start (BitVec 32))) "
            "((Start (BitVec 32) "
            "((store base index scale disp base mem bit) "
            "(formal-shadow base) (let-shadow base) base)))) "
            "(declare-var base (BitVec 32)) (declare-var index (BitVec 32)) "
            "(declare-var scale (BitVec 32)) (declare-var disp (BitVec 32)) "
            "(declare-var mem (BitVec 32)) (declare-var bit (BitVec 32)) "
            "(constraint (= (wrapped base index scale disp mem) mem)) "
            "(constraint (= (f base index scale disp mem bit) base)) (check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "0";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        const std::string smt = translation.toSmt2();
        assert(!has(smt, "(define-fun store "));
        assert(has(smt, "__somt_sygus_source_helper_"));
        ParserPtr parsed = newParser();
        assert(parsed->parseStr(smt));

        Sem::Assignment target;
        const Sem::ChoiceObservable& choice =
            translation.semantics().stages().front().projection.choices.front();
        bool found_store = false;
        for (const Sem::ChoiceAlternative& alternative : choice.alternatives) {
            const bool selected = has(
                alternative.label, "(store base index scale disp base mem bit)");
            target.emplace(alternative.target_name, selected ? "true" : "false");
            found_store = found_store || selected;
        }
        assert(found_store);
        Sem::Assignment source;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, source, diagnostics));
        assert(source.at("definition[f]")
               == "(define-fun f ((base (_ BitVec 32)) (index (_ BitVec 32)) "
                  "(scale (_ BitVec 32)) (disp (_ BitVec 32)) (mem (_ BitVec 32)) "
                  "(bit (_ BitVec 32))) (_ BitVec 32) "
                  "(store base index scale disp base mem bit))");
    }

    // A helper name that is built into the source BV logic remains unaliased
    // and rejected, so target-only alpha-renaming cannot admit an invalid
    // source signature.
    {
        Lang::SourceUnit unit;
        unit.main_path = "source-builtin-helper-collision.sl";
        unit.inline_source =
            "(set-logic BV) "
            "(define-fun bvadd ((x (BitVec 8))) (BitVec 8) x) "
            "(synth-fun f ((x (BitVec 8))) (BitVec 8) "
            "((Start (BitVec 8))) ((Start (BitVec 8) (x)))) "
            "(declare-var x (BitVec 8)) (constraint (= (f x) x)) (check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "0";
        const Translation translation = translate(unit, options);
        assert(!translation.ok());
    }

    // A helper defined after synth-fun is specialized per candidate, but that
    // must not let a source-logic builtin name evade signature validation.
    {
        Lang::SourceUnit unit;
        unit.main_path = "dependent-source-builtin-helper-collision.sl";
        unit.inline_source =
            "(set-logic BV) "
            "(synth-fun f ((x (BitVec 8))) (BitVec 8) "
            "((Start (BitVec 8))) ((Start (BitVec 8) (x)))) "
            "(define-fun bvadd ((x (BitVec 8))) (BitVec 8) (f x)) "
            "(declare-var x (BitVec 8)) (constraint (= (f x) x)) (check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "0";
        assert(!translate(unit, options).ok());
    }

    // A primed declaration reserves both x and x! as universal symbols; it
    // must reject clashes with prior synthesis or helper function names.
    {
        for (const std::string& function_name : {"x", "x!"}) {
            Lang::SourceUnit unit;
            unit.main_path = "primed-variable-synth-name-collision.sl";
            unit.inline_source =
                "(set-logic LIA) (synth-fun " + function_name
                + " () Int ((Start Int)) ((Start Int (0)))) "
                  "(declare-primed-var x Int) (check-synth)";
            TranslateOptions options;
            options.language_id = "sygus";
            options.profile_id = "bmc";
            options.parse.options["grammar_depth"] = "0";
            assert(!translate(unit, options).ok());
        }
        for (const std::string& function_name : {"x", "x!"}) {
            Lang::SourceUnit unit;
            unit.main_path = "primed-variable-helper-name-collision.sl";
            unit.inline_source =
                "(set-logic LIA) (define-fun " + function_name + " () Int 0) "
                "(synth-fun f () Int ((Start Int)) ((Start Int (0)))) "
                "(declare-primed-var x Int) (check-synth)";
            TranslateOptions options;
            options.language_id = "sygus";
            options.profile_id = "bmc";
            options.parse.options["grammar_depth"] = "0";
            assert(!translate(unit, options).ok());
        }
    }

    // The grammar bound is visible and has the sound under-approximation
    // direction: depth-one failure is not global unsynthesizability.
    {
        const Translation shallow = run(
            "languages/sygus/instances/ok/max2.sl", 1);
        assert(shallow.ok());
        assert(!has(shallow.toSmt2(), "(ite (<= x y) y x)"));
        bool found = false;
        for (const Fidelity::Bound& bound : shallow.report().fidelity().bounds) {
            found = found
                 || (bound.kind == Fidelity::Bound::GRAMMAR_RESTRICTION
                     && bound.value == 1 && bound.site == "max2");
        }
        assert(found);
        assert(shallow.report().fidelity().sound);
        assert(!shallow.report().fidelity().complete);
        assert(has(shallow.report().toJson(), "GRAMMAR_RESTRICTION"));
    }

    // SyGuS-IF's Variable production denotes all synth-fun parameters of the
    // matching sort. It is a finite terminal family, not a fresh SMT variable.
    {
        const Translation translation = run(
            "languages/sygus/instances/ok/identity-variable.sl", 0);
        assert(translation.ok());
        const auto& alternatives = translation.semantics().stages()
                                       .front().projection.choices.front().alternatives;
        assert(alternatives.size() == 1);
        assert(alternatives.front().label
               == "(define-fun id ((v Int)) Int v)");
    }

    // Source helper definitions remain definitions in the target relation;
    // the SMT parser checks their body and constraints use their exact meaning.
    {
        Lang::SourceUnit unit;
        unit.main_path = "helper-definition.sl";
        unit.inline_source =
            "(set-logic LIA) "
            "(define-fun successor ((v Int)) Int (+ v 1)) "
            "(synth-fun f ((x Int)) Int ((Start Int)) ((Start Int (x)))) "
            "(declare-var x Int) "
            "(constraint (= (successor x) (f x))) "
            "(check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "0";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        const std::string smt = translation.toSmt2();
        assert(has(smt, "successor"));
        assert(has(smt, "(successor x)"));
        assert(has(smt, "(forall ((x Int))"));
        ParserPtr parser = newParser();
        assert(parser->parseStr(smt));
    }

    // Omitting grammar_depth uses the exact finite-tree encoding, not a
    // hidden bounded search depth.
    {
        Lang::SourceUnit unit;
        unit.main_path = "languages/sygus/instances/ok/max2.sl";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        assert(translation.report().fidelity().complete);
        assert(has(translation.toSmt2(), "declare-datatypes"));
    }

    // Default LIA synthesis uses its logic-specific grammar. Arbitrary Int
    // constants are represented by existential target holes and projected back.
    {
        Lang::SourceUnit unit;
        unit.main_path = "default.sl";
        unit.inline_source =
            "(set-logic LIA) (synth-fun f ((x Int)) Int) "
            "(declare-var x Int) (constraint (= (f x) x)) (check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "1";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        const auto& alternatives = translation.semantics().stages()
                                       .front().projection.choices.front().alternatives;
        bool saw_hole = false;
        for (const Sem::ChoiceAlternative& alternative : alternatives) {
            saw_hole = saw_hole || !alternative.bindings.empty();
        }
        assert(saw_hole);
        Sem::Assignment target;
        const Sem::ChoiceAlternative* constant_candidate = nullptr;
        std::string placeholder;
        for (const Sem::ChoiceAlternative& alternative : alternatives) {
            target.emplace(alternative.target_name, "false");
            for (const Sem::ChoiceAlternative::Binding& binding : alternative.bindings) {
                target.emplace(binding.target_name, "0");
            }
            if (alternative.bindings.size() == 1
                && has(alternative.label,
                       " Int " + alternative.bindings.front().placeholder + ")")) {
                constant_candidate = &alternative;
                placeholder = alternative.bindings.front().placeholder;
            }
        }
        assert(constant_candidate != nullptr);
        target[constant_candidate->target_name] = "true";
        target[constant_candidate->bindings.front().target_name] = "17";
        Sem::Assignment source;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, source, diagnostics));
        assert(source.at("definition[f]") == "(define-fun f ((x Int)) Int 17)");
        ParserPtr projected_parser = newParser();
        assert(projected_parser->parseStr(source.at("definition[f]")));
        assert(translation.report().fidelity().sound);
        assert(!translation.report().fidelity().complete);
    }
    {
        const Translation translation = run(
            "languages/sygus/instances/reject/max2.sl", 2);
        assert(!translation.ok());
        assert(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    // A BV Constant production must return a literal in the source grammar,
    // after beta is composed through SMT lowering, with the original width.
    {
        Lang::SourceUnit unit;
        unit.display_name = "constant-bv.sl";
        unit.inline_source =
            "(set-logic BV) (synth-fun f ((x (_ BitVec 8))) (_ BitVec 8) "
            "((Start (_ BitVec 8))) "
            "((Start (_ BitVec 8) ((Constant (_ BitVec 8)))))) "
            "(declare-var x (_ BitVec 8)) "
            "(constraint (= (f x) #x2a)) (check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "0";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        const auto& alternatives = translation.semantics().stages()
                                       .front().projection.choices.front().alternatives;
        assert(alternatives.size() == 1);
        assert(alternatives.front().bindings.size() == 1);
        const auto& binding = alternatives.front().bindings.front();
        assert(binding.kind == Sem::ChoiceAlternative::Binding::Kind::BITVECTOR);
        assert(binding.bit_width == 8);
        Sem::Assignment target{{alternatives.front().target_name, "true"},
                               {binding.target_name, "(_ bv42 8)"}};
        Sem::Assignment source;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, source, diagnostics));
        assert(source.at("definition[f]") ==
               "(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) #b00101010)");
        ParserPtr parser = newParser();
        assert(parser->parseStr(source.at("definition[f]")));
    }

    // Every production is type checked even when no source constraint happens
    // to apply the synthesis function. Otherwise beta could return an invalid
    // define-fun from a target model satisfying only the selector axioms.
    {
        Lang::SourceUnit unit;
        unit.main_path = "wrong-sort.sl";
        unit.inline_source =
            "(set-logic ALL) "
            "(synth-fun f () Int ((Start Int)) ((Start Int (true)))) "
            "(check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "0";
        const Translation translation = translate(unit, options);
        assert(!translation.ok());
        assert(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(translation.diagnostics().all()[0].message,
                   "expected Int"));
    }

    // The 2015 invariant extension is elaborated to initiation, consecution,
    // and safety formulas over both current and primed state variables.
    {
        Lang::SourceUnit unit;
        unit.main_path = "invariant.sl";
        unit.inline_source =
            "(set-logic LIA) "
            "(synth-inv inv ((x Int)) ((Start Bool (true)))) "
            "(declare-primed-var x Int) "
            "(define-fun pre ((a Int)) Bool true) "
            "(define-fun trans ((a Int) (b Int)) Bool (= a b)) "
            "(define-fun post ((a Int)) Bool true) "
            "(inv-constraint inv pre trans post) (check-synth)";
        TranslateOptions options;
        options.language_id = "sygus";
        options.profile_id = "bmc";
        options.parse.options["grammar_depth"] = "1";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        const std::string smt = translation.toSmt2();
        assert(has(smt, "(forall ((x Int) (x! Int))"));
        ParserPtr parser = newParser();
        assert(parser->parseStr(smt));
    }

    // Compact target rendering may close a source helper over declare-var
    // inputs, but the projected witness must retain the original nullary
    // source call. Re-import the projected function with its source context.
    {
        std::string children;
        for (unsigned i = 0; i < 13; ++i) { children += " B"; }
        const std::string source =
            "(set-logic LIA) (declare-var g Int) "
            "(define-fun base () Bool (= g g)) "
            "(synth-fun f () Bool ((Start Bool ((and" + children + "))) "
            "(B Bool (base false)))) (constraint f) (check-synth)";
        const Translation translation = runInline(source);
        assert(translation.ok());
        const auto& stages = translation.semantics().stages();
        assert(!stages.front().projection.grammar_choices.empty());
        const auto& grammar = stages.front().projection.grammar_choices.front();
        Sem::Assignment target;
        for (const auto& node : grammar.nodes) {
            if (!node.selector_target.empty()) {
                target.emplace(node.selector_target, "0");
            }
        }
        Sem::Assignment projected;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, projected, diagnostics));
        const std::string expected = "(define-fun f () Bool (and";
        assert(has(projected.at("definition[f]"), expected));
        assert(!has(projected.at("definition[f]"), "__somt_sygus_universal_"));
        std::string source_context =
            "(set-logic LIA) (declare-const g Int) "
            "(define-fun base () Bool (= g g)) ";
        source_context += projected.at("definition[f]");
        source_context += " (assert f) (check-sat)";
        ParserPtr parser = newParser();
        assert(parser->parseStr(source_context));
    }

    // A target-only helper alias must be used by SMT rendering while source
    // projection returns the original helper name/signature.
    {
        std::string children;
        for (unsigned i = 0; i < 13; ++i) { children += " B"; }
        const std::string source =
            "(set-logic LIA) "
            "(define-fun int.to.str ((x Int)) Bool (= x 0)) "
            "(synth-fun f () Bool ((Start Bool ((and" + children + "))) "
            "(B Bool ((int.to.str 0) false)))) "
            "(constraint f) (check-synth)";
        const Translation translation = runInline(source);
        assert(translation.ok());
        const std::string target_smt = translation.toSmt2();
        assert(has(target_smt, "__somt_sygus_source_helper_"));
        ParserPtr target_parser = newParser();
        assert(target_parser->parseStr(target_smt));
        Sem::Assignment target;
        const auto& grammar =
            translation.semantics().stages().front().projection.grammar_choices.front();
        for (const auto& node : grammar.nodes) {
            if (!node.selector_target.empty()) {
                target.emplace(node.selector_target, "0");
            }
        }
        Sem::Assignment projected;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, projected, diagnostics));
        const std::string& witness = projected.at("definition[f]");
        assert(has(witness, "(int.to.str 0)"));
        assert(!has(witness, "__somt_sygus_source_helper_"));
        assert(has(source, "(define-fun int.to.str ((x Int)) Bool"));
        ParserPtr source_parser = newParser();
        assert(source_parser->parseStr(
            "(set-logic LIA) (define-fun int.to.str ((x Int)) Bool (= x 0)) "
            + witness + " (assert f) (check-sat)"));
    }

    // Repeated references to one nonterminal are distinct grammar
    // occurrences. The target model below chooses different productions for
    // the two B occurrences, then source projection reconstructs that term.
    {
        std::string fillers;
        for (unsigned i = 0; i < 13; ++i) { fillers += " C"; }
        const std::string source =
            "(set-logic LIA) (declare-var g Int) "
            "(synth-fun f ((x Int)) Bool "
            "((Start Bool ((and (xor B B)" + fillers + "))) "
            "(B Bool (true (= x 0))) (C Bool (true false)))) "
            "(constraint (= (f g) (not (= g 0)))) (check-synth)";
        const Translation translation = runInline(source);
        assert(translation.ok());
        const auto& grammar =
            translation.semantics().stages().front().projection.grammar_choices.front();
        Sem::Assignment target;
        unsigned b_occurrences = 0;
        for (const auto& node : grammar.nodes) {
            if (node.selector_target.empty()) { continue; }
            std::size_t selected = 0;
            // The compact circuit stores child expressions in separate nodes,
            // so this source production is represented by an equality
            // template with two child placeholders rather than `(= x 0)`.
            if (node.alternatives.size() == 2
                && node.alternatives[0].label == "true"
                && has(node.alternatives[1].label, "(= ")
                && node.alternatives[1].children.size() == 2) {
                selected = b_occurrences++ == 0 ? 0 : 1;
            }
            target.emplace(node.selector_target, std::to_string(selected));
        }
        assert(b_occurrences == 2);
        Sem::Assignment projected;
        Diagnostics diagnostics;
        assert(translation.semantics().project(target, projected, diagnostics));
        const std::string& witness = projected.at("definition[f]");
        assert(has(witness, "(xor true (= x 0))"));
        ParserPtr parser = newParser();
        assert(parser->parseStr("(set-logic LIA) (declare-const g Int) "
                                + witness
                                + " (assert (= (f g) (not (= g 0))))"));
    }

    const Lang::OpCoverage& coverage = language->coverage();
    assert(coverage.supported == 1 && coverage.total == 2);
    assert(coverage.missing.size() == coverage.total - coverage.supported);

    std::cout << "All SyGuS tests passed." << std::endl;
    return 0;
}
