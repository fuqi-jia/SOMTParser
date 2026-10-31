// The PDDL frontend, and the obligations docs/languages/pddl.md wrote down.
//
// **The frame problem is the largest implicit constraint in the whole batch**,
// and it is the one this file is mostly about. An action changes only the
// fluents its effects name; every OTHER fluent must be explicitly asserted
// unchanged across the step. Drop it and any fluent may take any value at any
// step, so the goal is reachable from anywhere in one step and the "plan"
// consists of nothing happening.
//
// The others, each also a wrong answer rather than a missing feature:
//
//   * a fluent not in `:init` is FALSE at step 0 -- PDDL states only what
//     holds, so leaving the rest free lets the plan start from a state the
//     problem does not describe;
//   * a precondition must hold in the state the action is applied TO;
//   * at most one action per step, which nothing in a domain file writes;
//   * a typed parameter ranges only over objects of its type.
//
// And the bound: planning asks whether a plan EXISTS, this asks whether one of
// length <= k does. `PLAN_HORIZON`, not `BMC_DEPTH` -- both count steps, of
// different things.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/languages/pddl_internal.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0, p = 0;
    while ((p = hay.find(needle, p)) != std::string::npos) { ++n; p += needle.size(); }
    return n;
}

Translation run(int horizon,
                const std::string& domain = "languages/pddl/instances/ok/gripper.pddl",
                const std::string& problem =
                    "languages/pddl/instances/ok/gripper.problem.pddl") {
    Lang::SourceUnit u;
    u.main_path = domain;
    u.display_name = domain;
    u.data_paths.push_back(problem);
    TranslateOptions opts;
    opts.language_id = "pddl";
    opts.profile_id = "bmc";
    opts.parse.options["plan_horizon"] = std::to_string(horizon);
    return translate(u, opts);
}

bool booleanValue(const std::shared_ptr<DAGNode>& node,
                  const std::map<std::string, bool>& values) {
    const auto child = [&](std::size_t i) { return booleanValue(node->getChild(i), values); };
    switch (node->getKind()) {
    case NODE_KIND::NT_CONST_TRUE: return true;
    case NODE_KIND::NT_CONST_FALSE: return false;
    case NODE_KIND::NT_VAR:
    case NODE_KIND::NT_TEMP_VAR: return values.at(node->getName());
    case NODE_KIND::NT_NOT: return !child(0);
    case NODE_KIND::NT_IMPLIES: return !child(0) || child(1);
    case NODE_KIND::NT_ITE: return child(0) ? child(1) : child(2);
    case NODE_KIND::NT_AND:
        for (std::size_t i = 0; i < node->getChildrenSize(); ++i) {
            if (!child(i)) { return false; }
        }
        return true;
    case NODE_KIND::NT_OR:
        for (std::size_t i = 0; i < node->getChildrenSize(); ++i) {
            if (child(i)) { return true; }
        }
        return false;
    case NODE_KIND::NT_EQ: return child(0) == child(1);
    case NODE_KIND::NT_XOR: return child(0) != child(1);
    default: VERIFY(false); return false;
    }
}

std::vector<std::map<std::string, bool>> booleanModels(const Translation& translation) {
    VERIFY(translation.ok());
    const auto parser = translation.parser();
    const auto variables = parser->getDeclaredVariables();
    const auto assertions = parser->getAssertions();
    VERIFY(variables.size() < 20);
    std::vector<std::map<std::string, bool>> models;
    for (unsigned bits = 0; bits < (1u << variables.size()); ++bits) {
        std::map<std::string, bool> values;
        for (std::size_t i = 0; i < variables.size(); ++i) {
            values.emplace(variables[i]->getName(), (bits & (1u << i)) != 0);
        }
        bool accepts = true;
        for (const auto& assertion : assertions) {
            if (!booleanValue(assertion, values)) { accepts = false; break; }
        }
        if (accepts) { models.push_back(std::move(values)); }
    }
    return models;
}

void checkGripperTransitionRelation() {
    const auto translation = run(1, "languages/pddl/instances/ok/gripper.pddl",
        "languages/pddl/instances/ok/gripper-frames.problem.pddl");
    const std::vector<std::string> source = {
        "at_ball1@1", "at_ball2@1", "holding_ball1@1", "holding_ball2@1",
        "do_pick_ball1@0", "do_pick_ball2@0", "do_drop_ball1@0", "do_drop_ball2@0",
        "__pddl_noop@0"};
    const auto project = [&](const std::map<std::string, bool>& values) {
        unsigned key = 0;
        for (std::size_t i = 0; i < source.size(); ++i) {
            // Both drop actions are unreachable in one source step and may
            // be eliminated. Every fluent and applicable choice must remain.
            if ((source[i] == "do_drop_ball1@0" || source[i] == "do_drop_ball2@0")
                && !values.count(source[i])) { continue; }
            if (values.at(source[i])) { key |= 1u << i; }
        }
        return key;
    };
    std::set<unsigned> observed;
    for (const auto& values : booleanModels(translation)) { observed.insert(project(values)); }
    // The source initial state has both balls on the floor. Only pick(ball1),
    // pick(ball2), or padding is applicable. Independently enumerate their
    // complete successor states, including every untouched fluent. Existential
    // enumeration above hides any target-only Boolean witnesses.
    std::set<unsigned> expected;
    for (const auto& action : {"do_pick_ball1@0", "do_pick_ball2@0", "__pddl_noop@0"}) {
        std::map<std::string, bool> values;
        for (const auto& name : source) { values[name] = false; }
        values["at_ball1@1"] = values["at_ball2@1"] = true;
        values[action] = true;
        if (std::string(action) == "do_pick_ball1@0") {
            values["at_ball1@1"] = false; values["holding_ball1@1"] = true;
        } else if (std::string(action) == "do_pick_ball2@0") {
            values["at_ball2@1"] = false; values["holding_ball2@1"] = true;
        }
        expected.insert(project(values));
    }
    VERIFY(observed == expected);
}

using IdentifierOccurrences = std::map<std::string, std::vector<Hir::ExprPtr>>;

IdentifierOccurrences identifierOccurrences(const Hir::ConstraintModel& model) {
    IdentifierOccurrences found;
    std::vector<Hir::ExprPtr> pending;
    for (const auto& constraint : model.constraints) { pending.push_back(constraint.formula); }
    for (const auto& objective : model.objectives) { pending.push_back(objective.term); }
    // Count uses, not just distinct nodes: every occurrence must share its leaf.
    while (!pending.empty()) {
        const auto expression = pending.back();
        pending.pop_back();
        if (expression->kind == Hir::ExprKind::IDENT) {
            found[expression->name].push_back(expression);
        }
        pending.insert(pending.end(), expression->args.begin(), expression->args.end());
    }
    return found;
}

void checkSharedPlanningIdentifiers(Lang::Language& language) {
    const std::string domain = R"((define (domain sharing)
      (:requirements :adl :action-costs) (:types item)
      (:constants a_b b - item)
      (:predicates (p ?x - item) (p_a ?x - item))
      (:functions (total-cost) - number)
      (:action turn :parameters (?choice - item)
        :precondition (forall (?x - item) (or (p ?x) (not (p ?x))))
        :effect (and
          (forall (?x - item) (and (when (p ?x) (not (p ?x)))
                                  (when (not (p ?x)) (p ?x))))
          (p_a b)
          (when (p ?choice) (increase (total-cost) 1.5))
          (when (not (p ?choice)) (increase (total-cost) 0.25))))))";
    const std::string problem = R"((define (problem sharing-problem) (:domain sharing)
      (:init (p a_b) (= (total-cost) 2))
      (:goal (forall (?x - item) (or (p ?x) (not (p ?x)))))
      (:metric minimize (total-cost))))";
    const auto build = [&]() {
        Diagnostics diagnostics;
        TranslationReport report;
        auto result = Lang::PddlInternal::buildClassicalEncoding(
            domain, problem, "shared-identifiers.pddl", 3, diagnostics, report);
        VERIFY(result.model);
        VERIFY(Hir::typeCheck(*result.model, diagnostics));
        return result;
    };
    const auto first = build();
    const auto second = build();
    const auto occurrences = identifierOccurrences(*first.model);
    const auto other = identifierOccurrences(*second.model);
    std::map<std::string, std::string> target;
    std::set<const Hir::Expr*> state_nodes;
    std::size_t state_symbols = 0, uses = 0;
    for (const auto& mapping : first.symbol_map) {
        if (mapping.source.compare(0, 6, "state[") != 0) { continue; }
        target.emplace(mapping.source, mapping.target);
        const auto& values = occurrences.at(mapping.target);
        VERIFY(values.size() > 1);
        for (const auto& value : values) { VERIFY(value == values.front()); }
        state_nodes.insert(values.front().get());
        VERIFY(values.front() != other.at(mapping.target).front());
        const auto expected = has(mapping.source, "(total-cost)")
            ? Hir::SortKind::REAL : Hir::SortKind::BOOL;
        VERIFY(values.front()->sort.kind == expected);
        uses += values.size();
        ++state_symbols;
    }
    // Three mutable Bool fluents and one Real accumulator at all four states.
    VERIFY(state_symbols == 16);
    VERIFY(state_nodes.size() == state_symbols);
    VERIFY(uses > state_symbols * 2);
    std::cout << "PDDL_IDENTIFIER_STATS {\"control\":\"bounded\",\"state_symbols\":"
              << state_symbols << ",\"identifier_references\":" << uses
              << ",\"unique_identifier_nodes\":" << state_nodes.size() << "}\n";
    // These source atoms have the same naive flattened spelling. Cache only
    // after the existing injective target allocator has separated them.
    VERIFY(target.at("state[0]::(p a_b)") != target.at("state[0]::(p_a b)"));
    const auto global = occurrences.at(target.at("state[0]::(p a_b)")).front();
    auto scoped = *first.model;
    Hir::Constraint constraint;
    constraint.formula = Hir::mkExists({{"local_cost", Hir::Sort::real()}},
        Hir::mkOp(Hir::Op::AND, {global, Hir::mkOp(Hir::Op::EQ,
            {Hir::mkBoundVar("local_cost", Hir::Sort::real()), Hir::mkReal("0")})}));
    scoped.constraints.push_back(std::move(constraint));
    TranslateOptions options;
    options.profile_id = "bmc";
    VERIFY(translate(scoped, options).ok());
    // HIR rejects a binder that shadows any global declaration. Sharing must
    // retain that diagnostic rather than reusing an unrelated successful check.
    scoped.constraints.back().formula = Hir::mkExists({{global->name, Hir::Sort::real()}},
        Hir::mkOp(Hir::Op::AND, {global, Hir::mkOp(Hir::Op::EQ,
            {Hir::mkBoundVar(global->name, Hir::Sort::real()), Hir::mkReal("0")})}));
    VERIFY(!translate(scoped, options).ok());
    // Neither the accepted scope nor the rejected shadow can mutate the shared
    // global Bool; the original snapshot remains reusable after lowering.
    VERIFY(global->kind == Hir::ExprKind::IDENT && global->sort.kind == Hir::SortKind::BOOL);
    VERIFY(translate(*first.model, options).ok());

    Lang::SourceUnit unit;
    unit.main_path = "languages/pddl/instances/ok/fond-retry.pddl";
    unit.data_paths = {"languages/pddl/instances/ok/fond-retry.problem.pddl"};
    Lang::ParseOptions policy;
    policy.options = {{"fond_policy", "strong-cyclic"}, {"policy_size", "2"}};
    const auto fond = language.parse(unit, policy);
    VERIFY(fond.ok());
    const auto policy_nodes = identifierOccurrences(*fond.model);
    std::set<const Hir::Expr*> fond_nodes;
    std::size_t fond_uses = 0;
    for (const auto& name : {"done@0", "done@1"}) {
        const auto& values = policy_nodes.at(name);
        VERIFY(values.size() > 1);
        fond_uses += values.size();
        fond_nodes.insert(values.front().get());
        for (const auto& value : values) {
            VERIFY(value == values.front() && value->sort.kind == Hir::SortKind::BOOL);
        }
    }
    VERIFY(fond_nodes.size() == 2);
    std::cout << "PDDL_IDENTIFIER_STATS {\"control\":\"fond\",\"state_symbols\":2,"
              << "\"identifier_references\":" << fond_uses
              << ",\"unique_identifier_nodes\":" << fond_nodes.size() << "}\n";
}

} // namespace

int main() {
    std::cout << "======= PDDL frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* p = Lang::LanguageRegistry::instance().byId("pddl");
    assert(p != nullptr);
    checkSharedPlanningIdentifiers(*p);
    // The problem file is the second half of the input, not a convenience --
    // without this translate() refuses the pair rather than letting a frontend
    // plan against no goal.
    assert(p->acceptsDataFiles());

    // A FOND witness is a state-feedback policy, with its own bound and beta.
    {
        Lang::SourceUnit unit;
        unit.main_path = "languages/pddl/instances/ok/fond-retry.pddl";
        unit.data_paths = {"languages/pddl/instances/ok/fond-retry.problem.pddl"};
        TranslateOptions options;
        options.language_id = "pddl";
        options.profile_id = "bmc";
        options.parse.options["fond_policy"] = "strong-cyclic";
        options.parse.options["policy_size"] = "2";
        const auto t = translate(unit, options);
        assert(t.ok());
        assert(t.semantics().stages()[0].decision.source
               == Sem::DecisionKind::REACTIVE_REALIZABILITY);
        Sem::Assignment target{
            {"__fond_active@0", "true"}, {"__fond_active@1", "true"},
            {"done@0", "false"}, {"done@1", "true"},
            {"do_try@0", "true"}, {"do_try@1", "false"},
            {"__fond_stop@0", "false"}, {"__fond_stop@1", "true"},
            {"__fond_rank@0", "1"}, {"__fond_rank@1", "0"},
        };
        Sem::Assignment source;
        Diagnostics diagnostics;
        assert(t.semantics().project(target, source, diagnostics));
        assert(source.at("policy-action[0]") == "(try)");
        assert(source.at("policy-state[1]::(done)") == "true");
        assert(source.at("policy-active[1]") == "true");
        assert(source.count("policy-action[1]") == 0);
        assert(source.count("__fond_rank@0") == 0);
    }

    // ---- Frames, effects, applicability and action cardinality. -------------
    checkGripperTransitionRelation();
    {
        const Translation t = run(1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- The closed-world assumption at step 0. ----------------------------
    {
        const std::string smt = run(1).toSmt2();
        // `:init` says (at ball1) (at ball2) and nothing else, so both holding
        // fluents are FALSE rather than free.
        assert(has(smt, "(assert at_ball1@0)"));
        assert(has(smt, "(assert (not holding_ball1@0))"));
        assert(has(smt, "(assert (not holding_ball2@0))"));
    }

    // ---- The precondition holds in the state the action is applied to. -----
    {
        const std::string smt = run(1).toSmt2();
        // Implied BY the action at THIS step -- not asserted unconditionally,
        // which would forbid states the plan may legitimately pass through.
        assert(has(smt, "(=> do_pick_ball1@0 at_ball1@0)"));
        assert(!has(smt, "(assert at_ball1@0)\n(assert at_ball1@0)"));
    }

    // ---- The horizon is the horizon. ---------------------------------------
    {
        const Translation a = run(1);
        const Translation b = run(2);
        assert(a.ok() && b.ok());
        assert(a.toSmt2() != b.toSmt2());
        // One more step of every fluent and every action.
        assert(count(b.toSmt2(), "at_ball1@") > count(a.toSmt2(), "at_ball1@"));
        // The goal is asserted at the LAST step, not the first.
        assert(has(a.toSmt2(), "(assert holding_ball1@1)"));
        assert(has(b.toSmt2(), "(assert holding_ball1@2)"));
    }

    // ---- beta returns a source plan, not internal one-hot variables. -------
    {
        const Translation t = run(1);
        assert(t.ok());
        Sem::Assignment target{
            {"do_pick_ball1@0", "true"},
            {"do_pick_ball2@0", "false"},
            {"do_drop_ball1@0", "false"},
            {"do_drop_ball2@0", "false"},
            {"__pddl_noop@0", "false"},
        };
        Sem::Assignment source;
        Diagnostics diags;
        assert(t.semantics().project(target, source, diags));
        assert(source.size() == 1);
        assert(source.at("plan[0]") == "(pick ball1)");
        assert(t.semantics().stages()[0].decision.source
               == Sem::DecisionKind::PLAN_EXISTENCE);
        assert(t.semantics().targetSatMeansSourceYes());
    }

    // ---- Typed parameters restrict the grounding. --------------------------
    {
        // Two types, one object each. `pick` takes a ball, so it grounds once
        // -- not twice. Untyped grounding would invent `pick table1`.
        Lang::SourceUnit u;
        u.main_path = "d.pddl";
        u.display_name = "d.pddl";
        u.inline_source =
            "(define (domain t)\n"
            "  (:requirements :typing :negative-preconditions)\n"
            "  (:types ball table)\n"
            "  (:predicates (at ?b - ball))\n"
            "  (:action pick :parameters (?b - ball) :precondition (at ?b)\n"
            "   :effect (not (at ?b))))\n";
        u.data_paths.push_back("languages/pddl/instances/ok/typed.problem.pddl");
        TranslateOptions opts;
        opts.language_id = "pddl";
        opts.profile_id = "bmc";
        opts.parse.options["plan_horizon"] = "1";
        const Translation t = translate(u, opts);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "do_pick_b1@0"));
        assert(!has(smt, "do_pick_t1@0"));
    }

    // ---- The bound is PLAN_HORIZON, and in the right direction. ------------
    {
        const Translation t = run(3);
        const EncodingChoice* c = nullptr;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "plan-existence") { c = &e; }
        }
        assert(c != nullptr);
        // sound and not complete: a plan found is real, "none of this length"
        // is not "unsolvable".
        assert(c->fidelity.sound && !c->fidelity.complete);
        assert(c->fidelity.bounds.size() == 1);
        // NOT BMC_DEPTH. Both count steps, of different things, and a results
        // table that conflated them would compare a planning bound with a
        // model-checking one.
        assert(c->fidelity.bounds[0].kind == Fidelity::Bound::PLAN_HORIZON);
        assert(c->fidelity.bounds[0].value == 3);
        assert(has(c->rationale, "UNSAT proves only"));
        // ...and the JSON names it, since that is what reaches the database.
        assert(has(t.report().toJson(), "PLAN_HORIZON"));
    }

    // ---- Refusals. ---------------------------------------------------------
    {
        // No problem file: a domain is a schema, and planning against no
        // objects and no goal would report success on half a problem.
        Lang::SourceUnit u;
        u.main_path = "languages/pddl/instances/ok/gripper.pddl";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "pddl";
        opts.profile_id = "bmc";
        opts.parse.options["plan_horizon"] = "1";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "no problem file"));
    }
    {
        Lang::SourceUnit u;
        u.main_path = "languages/pddl/instances/ok/gripper.pddl";
        u.display_name = u.main_path;
        u.data_paths.push_back("languages/pddl/instances/ok/gripper.problem.pddl");
        TranslateOptions opts;
        opts.language_id = "pddl";
        opts.profile_id = "bmc";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "no default"));
    }
    {
        // A plan shorter than k must remain representable even when its final
        // state is a dead end. The generated noop is forced to be a suffix,
        // and beta removes it rather than returning an invented PDDL action.
        const Translation t = run(
            2, "languages/pddl/instances/ok/deadend.pddl",
            "languages/pddl/instances/ok/deadend.problem.pddl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(=> __pddl_noop@0 __pddl_noop@1)"));
        assert(has(smt, "(=> __pddl_noop@1 (= done@1 done@2))"));
        Sem::Assignment target{
            {"do_finish@0", "true"}, {"__pddl_noop@0", "false"},
            {"do_finish@1", "false"}, {"__pddl_noop@1", "true"},
        };
        Sem::Assignment source;
        Diagnostics diags;
        assert(t.semantics().project(target, source, diags));
        assert(source.size() == 1);
        assert(source.at("plan[0]") == "(finish)");
    }

    {
        // The ADL successor-state relation evaluates all conditional-effect
        // guards in the old state. It expands finite quantifiers over the type
        // hierarchy and gives add effects precedence over simultaneous deletes.
        const Translation t = run(
            1, "languages/pddl/instances/ok/adl.pddl",
            "languages/pddl/instances/ok/adl.problem.pddl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(!has(smt, "do_update_c@0"));      // p(c) cannot hold before the first action
        assert(has(smt, "do_update_o@0"));
        assert(!has(smt, "q_c@0"));             // q is fixed by the closed initial state
        assert(!has(smt, "q_o@0"));
        const auto models = booleanModels(t);
        VERIFY(!models.empty());
        for (const auto& model : models) {
            // Only update(o) is initially applicable; its forall also sets
            // p(c). All dynamic fluents are true afterwards, including p(o)
            // whose simultaneous add takes precedence over its deletion.
            // The two static q facts are reconstructed from the initial state.
            VERIFY(model.at("do_update_o@0"));
            VERIFY(!model.at("__pddl_noop@0"));
            for (const auto& name : {"p_c@1", "p_o@1", "done@1"}) {
                VERIFY(model.at(name));
            }
        }

        const Sem::TranslationContract& contract = t.semantics().stages()[0];
        assert(contract.id == "pddl-to-typed-relational-core-v2");
        assert(!contract.source_signature.symbols.empty());
        assert(!contract.symbol_map.empty());
        assert(!contract.target_axioms.empty());
        assert(contract.source_signature.symbols.size() == contract.symbol_map.size());
    }

    {
        // Requirement declarations are part of source well-formedness. Using a
        // conditional effect without its requirement is an error, not a hidden
        // capability inference.
        Lang::SourceUnit u;
        u.main_path = "c.pddl";
        u.display_name = "c.pddl";
        u.inline_source =
            "(define (domain c) (:predicates (p))\n"
            "  (:action a :parameters () :effect (when (p) (not (p)))))\n";
        u.data_paths.push_back(
            "languages/pddl/instances/reject/missing_requirement.problem.pddl");
        TranslateOptions opts;
        opts.language_id = "pddl";
        opts.profile_id = "bmc";
        opts.parse.options["plan_horizon"] = "1";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        bool found_requirement = false;
        for (const Diagnostic& diagnostic : t.diagnostics().all()) {
            found_requirement = found_requirement
                             || has(diagnostic.message, ":conditional-effects");
        }
        assert(found_requirement);
    }

    // ---- Coverage is honest. -----------------------------------------------
    {
        const Lang::OpCoverage& cov = p->coverage();
        assert(cov.supported < cov.total);
        assert(cov.missing.size() == cov.total - cov.supported);
    }

    std::cout << "All PDDL tests passed." << std::endl;
    return 0;
}
