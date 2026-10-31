#include "somtparser/frontend/parser.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation run(const std::string& source, const std::string& mode = "unbounded",
                const std::string& depth = {}) {
    Lang::SourceUnit unit;
    unit.main_path = "unbounded-grammar.sl";
    unit.display_name = unit.main_path;
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "sygus";
    options.profile_id = "bmc";
    if (!mode.empty()) { options.parse.options["grammar_mode"] = mode; }
    if (!depth.empty()) { options.parse.options["grammar_depth"] = depth; }
    auto result = translate(unit, options);
    if (!result.ok()) {
        for (const auto& diagnostic : result.diagnostics().all()) {
            std::cerr << "SyGuS translation failed: " << diagnostic.message << '\n';
        }
    }
    return result;
}

bool has(const std::string& text, const std::string& part) {
    return text.find(part) != std::string::npos;
}

} // namespace

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // Reduced recursive-Int counterpart; the exact archived official task 1007 fixture follows below:
    // arbitrary constants plus recursive addition and subtraction.
    const std::string recursive_int =
        "(set-logic LIA) "
        "(synth-fun f ((x Int)) Int "
        " ((Const Int ((Constant Int) (+ Const Const) (- Const Const))))) "
        "(declare-var x Int) (constraint (= (f x) x)) (check-synth)";
    const Translation int_translation = run(recursive_int, "");
    if (!int_translation.ok()) {
        for (const auto& diagnostic : int_translation.diagnostics().all()) {
            std::cerr << "recursive Int SyGuS translation failed: "
                      << diagnostic.message << '\n';
        }
    }
    assert(int_translation.ok());
    assert(int_translation.report().fidelity().sound);
    assert(int_translation.report().fidelity().complete);
    assert(int_translation.report().fidelity().bounds.empty());
    assert(int_translation.report().fidelity().count_status == CountStatus::NO_GUARANTEE);
    assert(int_translation.semantics().stages().front().decision.target_unsat_meaning
           .find("full declared grammar") != std::string::npos);
    const std::string int_smt = int_translation.toSmt2();
    assert(has(int_smt, "declare-datatypes"));
    assert(has(int_smt, "define-funs-rec"));
    ParserPtr reparsed_int = newParser();
    assert(reparsed_int->parseStr(int_smt));

    // Exact archived task 1007, manifest SHA-256 c7dd5fdf84ceb06bde49855054cefb8dfdb2675dced46d608d639c4eef8b17b8.
    const std::string official_1007 = R"SYGUS((set-logic LIA)

(synth-fun inv ((x Int) (y Int) (z Int)) Bool
    ((Start Bool ((and AtomicFormula AtomicFormula) (or AtomicFormula AtomicFormula)))
    (AtomicFormula Bool ((<= Sum Const) (= Sum Const)))
    (Sum Int ((+ Term Term)))
    (Term Int ((* Sign Var)))
    (Sign Int (0 1 -1))
    (Var Int (x y z))
    (Const Int ((+ Const Const) (- Const Const) 0 1))))

(define-fun implies ((b1 Bool) (b2 Bool)) Bool
    (or (not b1) b2))
(define-fun and3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool
    (and (and b1 b2) b3))
(define-fun and4 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool)) Bool
    (and (and3 b1 b2 b3) b4))
(define-fun and5 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool)) Bool
    (and (and4 b1 b2 b3 b4) b5))
(define-fun and6 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool) (b6 Bool)) Bool
    (and (and5 b1 b2 b3 b4 b5) b6))
(define-fun or3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool
    (or (or b1 b2) b3))
(define-fun or4 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool)) Bool
    (or (or3 b1 b2 b3) b4))
(define-fun or5 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool)) Bool
    (or (or4 b1 b2 b3 b4) b5))
(declare-var s Int)
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var t Bool)
(declare-var x1 Int)
(declare-var z1 Int)
(constraint (implies (and (< x 100) (< z 100)) (inv x y z)))
(constraint (implies (and5 (inv x y z) (< x 100) (< 100 z) (implies t (and (= x1 (+ x 1)) (= z1 z))) (implies (not t) (and (= x1 (- x 1)) (= z1 (- z 1))))) (inv x1 y z1)))
(constraint (implies (and (inv x y z) (not (and (< x 100) (< 100 z)))) (or (>= x 100) (<= z 100))))

(check-synth)

)SYGUS";
    const Translation translated_1007 = run(official_1007, "");
    assert(translated_1007.ok());
    assert(has(translated_1007.toSmt2(), "define-funs-rec"));
    ParserPtr reparsed_1007 = newParser();
    assert(reparsed_1007->parseStr(translated_1007.toSmt2()));

    // Exact archived task 486, manifest SHA-256 e9dab92b85ae137505d81f42a828bd4c8e53bb67a0ec9daffdcd10d64c54e40b.
    const std::string official_486 = R"SYGUS((set-logic BV)

(define-fun origCir ((LN17 Bool) (k7 Bool) (LN34 Bool) (LN40 Bool) (LN56 Bool)) Bool
    (xor (and LN40 (xor (xor k7 LN17) LN34)) LN56))
(synth-fun skel ((LN17 Bool) (k7 Bool) (LN34 Bool) (LN40 Bool) (LN56 Bool)) Bool
    ((Start Bool ((and depth1 depth1) (not depth1) (or depth1 depth1) (xor depth1 depth1)))
    (depth1 Bool ((and depth2 depth2) (not depth2) (or depth2 depth2) (xor depth2 depth2)))
    (depth2 Bool ((and depth3 depth3) (not depth3) (or depth3 depth3) (xor depth3 depth3) LN34 LN40 LN56))
    (depth3 Bool ((and depth4 depth4) (not depth4) (or depth4 depth4) (xor depth4 depth4) LN17))
    (depth4 Bool (k7))))

(declare-var LN17 Bool)
(declare-var k7 Bool)
(declare-var LN34 Bool)
(declare-var LN40 Bool)
(declare-var LN56 Bool)
(constraint (= (origCir LN17 k7 LN34 LN40 LN56) (skel LN17 k7 LN34 LN40 LN56)))

(check-synth)

)SYGUS";
    const Translation translated_486 = run(official_486);
    assert(translated_486.ok());
    ParserPtr reparsed_486 = newParser();
    assert(reparsed_486->parseStr(translated_486.toSmt2()));
    const auto& int_projection = int_translation.semantics().stages().front().projection;
    assert(int_projection.choices.size() == 1);
    assert(int_projection.choices.front().alternatives.size() == 1);
    assert(int_projection.choices.front().alternatives.front().bindings.size() == 1);
    assert(int_projection.choices.front().alternatives.front().bindings.front().kind
           == Sem::ChoiceAlternative::Binding::Kind::SMT_TERM);
    Sem::Assignment projected_source;
    Sem::Assignment projected_target;
    const Sem::ChoiceAlternative& int_alternative =
        int_projection.choices.front().alternatives.front();
    projected_target.emplace(int_alternative.target_name, "true");
    projected_target.emplace(int_alternative.bindings.front().target_name,
                              "\"(+ 1 2)\"");
    Diagnostics projection_diagnostics;
    assert(int_translation.semantics().project(
        projected_target, projected_source, projection_diagnostics));
    assert(projected_source.at("definition[f]")
           == "(define-fun f ((x Int)) Int (+ 1 2))");
    Sem::Assignment malformed_target;
    malformed_target.emplace(int_alternative.target_name, "true");
    malformed_target.emplace(int_alternative.bindings.front().target_name,
                             "\"(+ 1 2) (- 2 1)\"");
    Sem::Assignment rejected_source;
    Diagnostics malformed_projection_diagnostics;
    assert(!int_translation.semantics().project(
        malformed_target, rejected_source, malformed_projection_diagnostics));

    // Mirrors the finite, stratified Boolean grammar used by official case 486.
    // It still takes the same unbounded AST path and needs no depth cap.
    const std::string recursive_bool =
        "(set-logic LIA) "
        "(synth-fun p ((x Bool)) Bool "
        " ((Start Bool (true false x (not Start) "
        "(and (Constant Bool) Start))))) "
        "(declare-var x Bool) "
        "(constraint (= (p x) x)) (check-synth)";
    const Translation bool_translation = run(recursive_bool);
    assert(bool_translation.ok());
    const std::string bool_smt = bool_translation.toSmt2();
    assert(has(bool_smt, "declare-datatypes"));
    ParserPtr reparsed_bool = newParser();
    assert(reparsed_bool->parseStr(bool_smt));

    // Nested literal nodes are metadata-bearing parts of one constructor.
    // Multiple Constant leaves must each get their own selector and neither
    // may escape as a free grammar_literal marker in the emitted SMT.
    const Translation nested_bool_constants = run(
        "(set-logic LIA) "
        "(synth-fun q () Bool "
        " ((Start Bool ((and (Constant Bool) (Constant Bool))))) ) "
        "(constraint (= (q) true)) (check-synth)");
    assert(nested_bool_constants.ok());
    const std::string nested_bool_smt = nested_bool_constants.toSmt2();
    assert(nested_bool_smt.find("__somt_sygus_grammar_literal_") == std::string::npos);
    ParserPtr reparsed_nested_bool = newParser();
    assert(reparsed_nested_bool->parseStr(nested_bool_smt));

    // A grammar parameter and a free declare-var with the same source spelling
    // are distinct bindings. The helper closes over the global, while the
    // grammar's direct x denotes the synth-fun parameter.
    const Translation closure_collision = run(
        "(set-logic LIA) (declare-var x Int) "
        "(define-fun bump ((a Int)) Int (+ a x)) "
        "(synth-fun f ((x Int)) Int ((Start Int ((bump x) (Constant Int))))) "
        "(constraint (= (f x) x)) (check-synth)");
    assert(closure_collision.ok());
    const std::string closure_smt = closure_collision.toSmt2();
    ParserPtr reparsed_closure = newParser();
    assert(reparsed_closure->parseStr(closure_smt));

    // A quoted parameter whose decoded name is a builtin token stays a value
    // occurrence; parameter alpha-renaming must leave the (not ...) head intact.
    const Translation quoted_parameter = run(
        "(set-logic LIA) (declare-var v Bool) "
        "(synth-fun q ((|and| Bool)) Bool "
        " ((Start Bool (|and| (not Start))))) "
        "(constraint (= (q v) v)) (check-synth)");
    assert(quoted_parameter.ok());
    ParserPtr reparsed_quoted = newParser();
    assert(reparsed_quoted->parseStr(quoted_parameter.toSmt2()));

    // Variable is a grammar macro at any expression position, not just when
    // it is itself the whole production.
    const Translation nested_variable = run(
        "(set-logic LIA) (synth-fun inc ((x Int)) Int "
        " ((Start Int ((+ (Variable Int) 1))))) "
        "(declare-var x Int) (constraint (= (inc x) (+ x 1))) (check-synth)");
    assert(nested_variable.ok());
    ParserPtr reparsed_nested_variable = newParser();
    assert(reparsed_nested_variable->parseStr(nested_variable.toSmt2()));

    // Supplying grammar_depth preserves the historic finite under-approximation.
    const Translation bounded = run(recursive_int, "bounded", "1");
    assert(bounded.ok());
    assert(!bounded.report().fidelity().complete);
    bool recorded_grammar_bound = false;
    for (const auto& bound : bounded.report().fidelity().bounds) {
        recorded_grammar_bound = recorded_grammar_bound
            || bound.kind == Fidelity::Bound::GRAMMAR_RESTRICTION;
    }
    assert(recorded_grammar_bound);
    assert(!has(bounded.toSmt2(), "declare-datatypes"));

    // Conflicting and misspelled mode options fail explicitly.
    assert(!run(recursive_int, "unbounded", "2").ok());
    assert(!run(recursive_int, "bounded").ok());
    assert(!run(recursive_int, "automatic").ok());

    // A recursive cycle with no finite tree has an empty grammar language and
    // becomes an explicit target contradiction rather than a depth-based guess.
    const Translation empty_language = run(
        "(set-logic LIA) (synth-fun z () Int ((A Int (A)))) "
        "(constraint (= z 0)) (check-synth)");
    assert(empty_language.ok());
    assert(empty_language.report().fidelity().complete);
    assert(has(empty_language.toSmt2(), "(assert false)"));

    // A sole String Constant production denotes every String value, so the
    // direct-value encoding needs no recursive String renderer.
    const Translation string_constant = run(
        "(set-logic SLIA) (synth-fun s () String "
        " ((Start String ((Constant String))))) "
        "(constraint (= s \"a\")) (check-synth)");
    assert(string_constant.ok());
    assert(has(string_constant.toSmt2(), "__somt_sygus_witness_value_"));
    assert(!has(string_constant.toSmt2(), "str.replace_all"));
}
