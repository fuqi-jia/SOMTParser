#include "somtparser/languages/sygus.h"
#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

using namespace SOMTParser;
namespace Sem = Uir::Sem;

int main() {
    // The new retention policy keeps executable definitions without changing
    // the existing equation policy used by other frontend callers.
    auto parser = newParser();
    VERIFY(parser->parseStr("(declare-const x Bool) "
        "(define-fun add_one ((x Int)) Int (+ x 1)) "
        "(assert (and x (= (add_one 2) 3)))"));
    Uir::Hir::ConstraintModel retained, equations;
    Uir::Diagnostics retained_diagnostics, equation_diagnostics;
    Lower::ParserToHir retained_lifter(parser), equation_lifter(parser);
    VERIFY(retained_lifter.lift(retained, retained_diagnostics, true));
    VERIFY(equation_lifter.lift(equations, equation_diagnostics));
    VERIFY(retained.funs.size() == 1 && retained.funs[0].body);
    VERIFY(retained.funs[0].binders.size() == 1);
    VERIFY(retained.funs[0].binders[0].name != "x");
    VERIFY(retained.constraints.size() == 1);
    VERIFY(equations.funs.size() == 1 && !equations.funs[0].body);
    VERIFY(equations.constraints.size() == 2);
    Lang::LanguageRegistry::instance().add(Lang::mkSygusLanguage());
    Lang::SourceUnit unit;
    unit.display_name = "joint-witnesses.sl";
    unit.inline_source =
        "(set-logic ALL) "
        "(synth-fun flag () Bool ((S Bool ((Constant Bool))))) "
        "(synth-fun num () Int ((S Int ((Constant Int))))) "
        "(synth-fun bits () (_ BitVec 4) ((S (_ BitVec 4) ((Constant (_ BitVec 4)))))) "
        "(synth-fun text () String ((S String ((Constant String))))) "
        "(constraint flag) (constraint (= num (- 7))) "
        "(constraint (= bits #xa)) (constraint (= text \"a\")) (check-synth)";
    TranslateOptions options;
    options.language_id = "sygus";
    options.profile_id = "bmc";
    options.parse.options["grammar_mode"] = "unbounded";
    auto result = translate(unit, options);
    VERIFY(result.ok());
    const auto& stage = result.semantics().stages().front();
    VERIFY(stage.projection.choices.size() == 4);
    Sem::Assignment target;
    for (const auto& observable : stage.projection.choices) {
        VERIFY(observable.alternatives.size() == 1);
        const auto& alternative = observable.alternatives.front();
        target[alternative.target_name] = "true";
        VERIFY(alternative.bindings.size() == 1);
        const auto& binding = alternative.bindings.front();
        if (observable.source_name == "definition[flag]") {
            VERIFY(binding.kind == Sem::ChoiceAlternative::Binding::Kind::BOOLEAN);
            target[binding.target_name] = "true";
        } else if (observable.source_name == "definition[num]") {
            VERIFY(binding.kind == Sem::ChoiceAlternative::Binding::Kind::INTEGER);
            target[binding.target_name] = "(- 7)";
        } else if (observable.source_name == "definition[bits]") {
            VERIFY(binding.kind == Sem::ChoiceAlternative::Binding::Kind::BITVECTOR);
            VERIFY(binding.bit_width == 4);
            target[binding.target_name] = "#xa";
        } else {
            VERIFY(observable.source_name == "definition[text]");
            VERIFY(binding.kind == Sem::ChoiceAlternative::Binding::Kind::SMT_STRING_VALUE);
            target[binding.target_name] = "\"a\"";
        }
    }
    Sem::Assignment source;
    Uir::Diagnostics diagnostics;
    VERIFY(result.semantics().project(target, source, diagnostics));
    VERIFY(source.at("definition[flag]") == "(define-fun flag () Bool true)");
    VERIFY(source.at("definition[num]") == "(define-fun num () Int (- 7))");
    VERIFY(source.at("definition[bits]") == "(define-fun bits () (_ BitVec 4) #xa)");
    VERIFY(source.at("definition[text]") == "(define-fun text () String \"a\")");
}
