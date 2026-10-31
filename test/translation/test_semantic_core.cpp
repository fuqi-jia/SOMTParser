#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/translation/semantics.h"
#include "somtparser/hir/typecheck.h"

#include <algorithm>
#include <iostream>
#include <string>
#include <type_traits>
#include <utility>
#include <utility>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;
namespace S = SOMTParser::Uir::Sem;

namespace {

bool has(const std::string& text, const std::string& part) {
    return text.find(part) != std::string::npos;
}

H::ConstraintModel relationalExample() {
    H::ConstraintModel model;
    model.decls.push_back({"x", H::Sort::integer(), H::mkInt(0), H::mkInt(10), {}});
    model.decls.push_back({"b", H::Sort::boolean(), {}, {}, {}});

    const H::ExprPtr x = H::mkIdent("x", H::Sort::integer());
    const H::ExprPtr b = H::mkIdent("b", H::Sort::boolean());
    S::RelationalBuilder relational;
    const H::ExprPtr domain = H::mkOp(H::Op::NOT,
                                      {H::mkOp(H::Op::EQ, {x, H::mkInt(0)})});
    const H::ExprPtr quotient =
        relational.value(H::Op::DIV_TRUNC, {H::mkInt(10), x}, {}, domain);
    const H::ExprPtr equality =
        relational.predicate(H::Op::EQ, {quotient, H::mkInt(10)});
    H::Constraint constraint;
    constraint.formula = relational.boolean(H::Op::IMPLIES, {b, equality});
    model.constraints.push_back(std::move(constraint));

    model.objectives.push_back(
        {H::ObjKind::MINIMIZE, x, "obj0", {}});
    return model;
}

} // namespace

int main() {
    static_assert(std::is_aggregate_v<EncodingChoice>,
                  "EncodingChoice remains aggregate-initializable");
    static_assert(std::is_aggregate_v<S::ProofObligation>,
                  "ProofObligation remains aggregate-initializable");
    static_assert(std::is_same_v<S::EvidenceKind, EvidenceKind>,
                  "the old Sem-scoped EvidenceKind name remains an alias");
    const S::ProofObligation legacy_obligation{
        S::ProofObligationKind::SOUNDNESS, EvidenceKind::PENDING,
        "legacy three-field aggregate"};
    VERIFY(legacy_obligation.evidence_refs.empty());
    const EncodingChoice legacy_choice{
        "site", "op", "strategy", Fidelity::exact(), "legacy five-field aggregate"};
    VERIFY(!legacy_choice.count_evidence.has_value());
    std::cout << "======= semantic configuration and relational core =======\n";

    {
        const S::AssumptionProfile mzn = S::AssumptionProfile::miniZinc();
        const S::AssumptionProfile smt = S::AssumptionProfile::smtLib();
        VERIFY(mzn.functions == S::FunctionSemantics::PARTIAL);
        VERIFY(mzn.carrier_emptiness == S::CarrierEmptiness::MIXED);
        VERIFY(mzn.undefined == S::UndefinedSemantics::RELATIONAL_FALSE);
        VERIFY(mzn.division == S::DivisionSemantics::TRUNCATE_TOWARD_ZERO);
        VERIFY(mzn.arrays == S::ArraySemantics::FINITE_PARTIAL);
        VERIFY(smt.functions == S::FunctionSemantics::TOTAL);
        VERIFY(smt.carrier_emptiness == S::CarrierEmptiness::NONEMPTY);
        VERIFY(smt.division == S::DivisionSemantics::EUCLIDEAN);
        VERIFY(smt.arrays == S::ArraySemantics::TOTAL_EXTENSIONAL);

        const S::AssumptionProfile fzn = S::AssumptionProfile::flatZinc();
        const S::AssumptionProfile essence = S::AssumptionProfile::essencePrime();
        const S::AssumptionProfile xcsp = S::AssumptionProfile::xcsp3();
        VERIFY(fzn.annotations == S::AnnotationSemantics::MIXED);
        VERIFY(fzn.quantifiers == S::QuantifierSemantics::NONE);
        VERIFY(essence.undefined == S::UndefinedSemantics::RELATIONAL_FALSE);
        VERIFY(essence.quantifiers == S::QuantifierSemantics::FINITE_EXPANSION);
        VERIFY(xcsp.division == S::DivisionSemantics::TRUNCATE_TOWARD_ZERO);
        VERIFY(xcsp.arrays == S::ArraySemantics::FIXED_VECTOR);
    }

    {
        // A source Institution exists independently of parse success. This is
        // what lets the framework state the accepted synthesis fragments and
        // refuse reductions that would answer a different question.
        const std::vector<std::string> ids = {
            "hddl", "pddl", "sygus", "syntcomp", "moxi", "vmt", "aiger",
            "btor2", "essence", "boogie", "smtlib2", "chc", "minizinc",
            "qcir", "qdimacs", "dimacs", "wcnf", "opb", "lp", "mps",
            "flatzinc", "tptp", "xcsp3", "cryptoline",
        };
        for (const std::string& id : ids) {
            const S::SourceSemanticSpec spec = S::sourceSemanticSpec(id);
            VERIFY(spec.valid());
            VERIFY(spec.institution.id == (id == "essence" ? "essence-prime" : id));
        }
        VERIFY(!S::sourceSemanticSpec("not-a-language").valid());

        const S::SourceSemanticSpec hddl = S::sourceSemanticSpec("hddl");
        VERIFY(hddl.smt_embedding
               == S::SmtEmbeddingKind::BOUNDED_UNDER_APPROXIMATION);
        VERIFY(hddl.required_bounds.size() == 2);
        VERIFY(hddl.required_bounds[0] == Fidelity::Bound::PLAN_HORIZON);
        VERIFY(hddl.required_bounds[1]
               == Fidelity::Bound::DECOMPOSITION_DEPTH);

        const S::SourceSemanticSpec sygus = S::sourceSemanticSpec("sygus");
        VERIFY(sygus.supports(S::DecisionKind::FUNCTION_SYNTHESIS));
        VERIFY(sygus.required_bounds.size() == 1);
        VERIFY(sygus.required_bounds[0]
               == Fidelity::Bound::GRAMMAR_RESTRICTION);

        const S::SourceSemanticSpec syntcomp =
            S::sourceSemanticSpec("syntcomp");
        VERIFY(syntcomp.supports(S::DecisionKind::REACTIVE_REALIZABILITY));
        VERIFY(syntcomp.smt_embedding
               == S::SmtEmbeddingKind::DIRECT_REDUCTION);
        VERIFY(syntcomp.required_bounds.empty());

        const S::SourceSemanticSpec minizinc =
            S::sourceSemanticSpec("minizinc");
        VERIFY(minizinc.supports(S::DecisionKind::SATISFIABILITY));
        VERIFY(minizinc.supports(S::DecisionKind::OPTIMIZATION));
        VERIFY(!minizinc.supports(S::DecisionKind::VALIDITY));

        H::ConstraintModel empty;
        S::TranslationContract pddl_contract =
            S::pddlToRelationalContract(empty, Fidelity::exact(), {});
        Diagnostics missing_bound;
        VERIFY(!S::validateSourceContract(
            S::sourceSemanticSpec("pddl"), pddl_contract, missing_bound));
        VERIFY(missing_bound.hasErrors());

        pddl_contract.claimed_fidelity = Fidelity::underApprox(
            {Fidelity::Bound::PLAN_HORIZON, 3, "test"});
        Diagnostics bounded;
        VERIFY(S::validateSourceContract(
            S::sourceSemanticSpec("pddl"), pddl_contract, bounded));
        VERIFY(!bounded.hasErrors());

        auto policy_contract = S::pddlToRelationalContract(empty,
            Fidelity::underApprox({Fidelity::Bound::PLAN_HORIZON, 3, "test"}),
            {}, {}, {}, {}, "strong-cyclic");
        Diagnostics wrong_policy_bound;
        VERIFY(!S::validateSourceContract(S::sourceSemanticSpec("pddl"),
                                         policy_contract, wrong_policy_bound));
        policy_contract.claimed_fidelity = Fidelity::underApprox(
            {Fidelity::Bound::STRATEGY_SIZE, 3, "test"});
        Diagnostics policy_bound;
        VERIFY(S::validateSourceContract(S::sourceSemanticSpec("pddl"),
                                        policy_contract, policy_bound));

        const S::SourceSemanticSpec sygus_spec = S::sourceSemanticSpec("sygus");
        VERIFY(sygus_spec.smt_embedding == S::SmtEmbeddingKind::DIRECT_REDUCTION);
        H::ConstraintModel no_sygus_constraints;
        auto unbounded_sygus = S::sygusToRelationalContract(
            no_sygus_constraints, Fidelity::exact(), {});
        Diagnostics exact_sygus_diagnostics;
        VERIFY(S::validateSourceContract(sygus_spec, unbounded_sygus,
                                         exact_sygus_diagnostics));

        Fidelity incomplete_without_bound = Fidelity::exact();
        incomplete_without_bound.complete = false;
        auto incomplete_sygus = S::sygusToRelationalContract(
            no_sygus_constraints, incomplete_without_bound, {});
        Diagnostics missing_sygus_bound;
        VERIFY(!S::validateSourceContract(sygus_spec, incomplete_sygus,
                                          missing_sygus_bound));
        VERIFY(missing_sygus_bound.hasErrors());

        Fidelity unsound_without_bound = Fidelity::exact();
        unsound_without_bound.sound = false;
        auto unsound_sygus = S::sygusToRelationalContract(
            no_sygus_constraints, unsound_without_bound, {});
        Diagnostics unsound_missing_bound;
        VERIFY(!S::validateSourceContract(sygus_spec, unsound_sygus,
                                          unsound_missing_bound));

        auto bounded_sygus = S::sygusToRelationalContract(
            no_sygus_constraints,
            Fidelity::underApprox({Fidelity::Bound::GRAMMAR_RESTRICTION,
                                   3, "f"}), {});
        Diagnostics bounded_sygus_diagnostics;
        VERIFY(S::validateSourceContract(sygus_spec, bounded_sygus,
                                         bounded_sygus_diagnostics));
        VERIFY(!bounded_sygus_diagnostics.hasErrors());

    }

    {
        // A conditional is lazy: an undefined unselected branch cannot make
        // the whole expression undefined. Its definition is
        // `ite(condition, def(then), def(else))`, not their conjunction.
        S::RelationalBuilder relational;
        const H::ExprPtr x = H::mkIdent("x", H::Sort::integer());
        const H::ExprPtr b = H::mkIdent("b", H::Sort::boolean());
        const H::ExprPtr domain = H::mkOp(
            H::Op::NOT, {H::mkOp(H::Op::EQ, {x, H::mkInt(0)})});
        const H::ExprPtr quotient = relational.value(
            H::Op::DIV_TRUNC, {H::mkInt(10), x}, {}, domain);
        const H::ExprPtr selected = relational.conditional(
            b, H::mkInt(1), quotient);
        const S::PartialExpr partial = relational.inspect(selected);
        VERIFY(partial.defined->kind == H::ExprKind::OP);
        VERIFY(partial.defined->op == H::Op::ITE);
        VERIFY(partial.defined->args.size() == 3);
        VERIFY(partial.defined->args[1]->kind == H::ExprKind::LIT_BOOL);
        VERIFY(partial.defined->args[1]->bool_value);
    }

    {
        // A total conditional must not be retained by the partiality table
        // after its caller discards it. This matters for repeated elaboration
        // of fixed record fields and generator probes in large models.
        S::RelationalBuilder relational;
        const auto condition = H::mkIdent("condition", H::Sort::boolean());
        std::weak_ptr<const H::Expr> temporary;
        {
            const auto selected = relational.conditional(
                condition, H::mkInt(1), H::mkInt(2));
            const auto definition = relational.inspect(selected).defined;
            VERIFY(definition->kind == H::ExprKind::LIT_BOOL);
            VERIFY(definition->bool_value);
            temporary = selected;
        }
        VERIFY(temporary.expired());

        const auto guard = H::mkIdent("guard", H::Sort::boolean());
        const auto partial = relational.remember({guard, H::mkInt(3)});
        const auto fixed = relational.conditional(
            H::mkBool(true), H::mkInt(1), partial);
        VERIFY(relational.inspect(fixed).defined->kind == H::ExprKind::LIT_BOOL);
        VERIFY(relational.inspect(fixed).defined->bool_value);
        const auto shared = relational.conditional(condition, partial, partial);
        VERIFY(relational.inspect(shared).defined == guard);

        // Simplifying branch guards cannot erase an undefined test, even
        // when its stored Boolean value happens to be a literal.
        const auto undefined_condition = relational.remember(
            {H::mkBool(false), H::mkBool(true)});
        const auto undefined = relational.conditional(
            undefined_condition, H::mkInt(1), H::mkInt(2));
        VERIFY(relational.inspect(undefined).defined->kind == H::ExprKind::LIT_BOOL);
        VERIFY(!relational.inspect(undefined).defined->bool_value);
    }

    H::ConstraintModel model = relationalExample();
    {
        // Identity lowering has a direct bijection, but a positive count claim
        // is accepted only with explicit evidence attached to the contract.
        H::ConstraintModel identity;
        identity.decls.push_back({"b", H::Sort::boolean(), {}, {}, {}});
        S::TranslationContract contract = S::relationalToSmtContract(identity, false);
        contract.claimed_fidelity.count_status = CountStatus::PRESERVED;
        Diagnostics missing_count;
        VERIFY(!contract.validate(missing_count));
        VERIFY(missing_count.hasErrors());

        contract.obligations.push_back(
            {S::ProofObligationKind::MODEL_COUNT, EvidenceKind::PENDING,
             "identity source and target variable map", {"test/translation/test_semantic_core.cpp"}});
        Diagnostics pending_count;
        VERIFY(!contract.validate(pending_count));
        VERIFY(pending_count.hasErrors());

        contract.obligations.back() = {
            S::ProofObligationKind::MODEL_COUNT, EvidenceKind::BY_CONSTRUCTION,
            "same Boolean symbol on source and target; no target-only symbols or axioms, so identity gives one extension per source assignment",
            {""}};
        Diagnostics empty_reference;
        VERIFY(!contract.validate(empty_reference));
        VERIFY(empty_reference.hasErrors());

        contract.obligations.back().evidence_refs = {
            "test/translation/test_semantic_core.cpp::identity-count-contract"};
        Diagnostics evidenced_count;
        VERIFY(contract.validate(evidenced_count));
        VERIFY(!evidenced_count.hasErrors());
    }
    {
        Diagnostics diags;
        VERIFY(H::typeCheck(model, diags));
        ParserPtr parser = newParser();
        Lower::HirToParser lowering(parser);
        TranslationReport report;
        VERIFY(lowering.lower(model, report, diags));
        VERIFY(!diags.hasErrors());
        const std::string smt = parser->dumpSMT2();
        VERIFY(has(smt, "(=> b (and (distinct 0 x)"));
        // The domain condition is local to the consequent, not a global x!=0.
        VERIFY(!has(smt, "(assert (distinct 0 x))"));
    }

    {
        S::TranslationPipeline pipeline;
        pipeline.add(S::miniZincToRelationalContract(model));
        pipeline.add(S::relationalToSmtContract(model, true));
        Diagnostics diags;
        VERIFY(pipeline.validate(diags));
        VERIFY(!diags.hasErrors());
        VERIFY(pipeline.fidelity().count_status == CountStatus::UNASSESSED);
        VERIFY(pipeline.stages().front().source.surface_language == "MiniZinc");
        VERIFY(pipeline.stages().front().sentence_translation_id
               == "minizinc-elaboration-to-typed-relational-sentences-v1");
        VERIFY(!pipeline.stages().front().source.sentence_space.empty());
        VERIFY(!pipeline.stages().front().source.model_class.empty());
        VERIFY(!pipeline.stages().front().source.satisfaction_relation.empty());
        VERIFY(!pipeline.stages().front().sort_map.empty());
        VERIFY(pipeline.stages().front().target_axioms.size() == 1);
        VERIFY(pipeline.stages().back().target.id == "omt");
        VERIFY(pipeline.stages().back().objectives.source == S::ObjectiveOrder::MINIMIZE);
        VERIFY(pipeline.stages().back().objectives.source_directions.size() == 1);
        VERIFY(pipeline.stages().back().objectives.source_directions.front()
               == H::ObjKind::MINIMIZE);
        VERIFY(pipeline.stages().back().objectives.value_map_id == "identity");
    }

    {
        S::TranslationContract missing_alpha =
            S::miniZincToRelationalContract(model);
        missing_alpha.sentence_translation_id.clear();
        Diagnostics diags;
        VERIFY(!missing_alpha.validate(diags));
        VERIFY(diags.hasErrors());
    }

    {
        // A symbol name is not a signature morphism by itself. The target must
        // contain the mapped symbol at the mapped type.
        S::TranslationContract missing = S::miniZincToRelationalContract(model);
        missing.symbol_map.front().target = "not-declared";
        Diagnostics diags;
        VERIFY(!missing.validate(diags));
        VERIFY(diags.hasErrors());
    }

    {
        S::TranslationContract ill_sorted =
            S::miniZincToRelationalContract(model);
        S::Signature changed = ill_sorted.target_signature.materialize();
        changed.symbols.front().codomain = H::Sort::boolean();
        ill_sorted.target_signature = S::SignatureSnapshot(std::move(changed));
        Diagnostics diags;
        VERIFY(!ill_sorted.validate(diags));
        VERIFY(diags.hasErrors());
    }

    {
        // A snapshot is an immutable shared view. Materializing it gives an
        // independent mutable Signature and cannot alter another copy.
        S::Signature owning_signature;
        owning_signature.symbols.push_back(
            {"owned", S::SymbolKind::CONSTANT, {}, H::Sort::integer()});
        S::Signature owning_copy = owning_signature;
        owning_copy.symbols.front().name = "copy-only";
        VERIFY(owning_signature.symbols.front().name == "owned");
        S::SignatureSnapshot lvalue_snapshot(owning_signature);
        owning_signature.symbols.front().name = "owner-mutated";
        VERIFY(lvalue_snapshot.symbols.front().name == "owned");

        H::ConstraintModel snapshot_model = relationalExample();
        S::SignatureSnapshot snapshot(S::signatureOf(snapshot_model));
        S::SignatureSnapshot shared = snapshot;
        S::Signature edit = shared.materialize();
        edit.symbols.front().name = "edited-only";
        VERIFY(snapshot.symbols.front().name == "x");
        VERIFY(shared.symbols.front().name == "x");
        VERIFY(edit.symbols.front().name == "edited-only");

        // Moving an individual public read-only view out of a snapshot must
        // not make partial snapshots qualify for index reuse.
        S::SignatureSnapshot partial = snapshot;
        auto extracted_symbols = std::move(partial.symbols);
        VERIFY(extracted_symbols.size() == snapshot.symbols.size());
        VERIFY(!partial.sharesStorageWith(snapshot));

        // Matching is an exact ordered, sort-aware check. A valid hint can be
        // reused; any name/sort/order difference forces model reconstruction.
        VERIFY(S::signatureMatchesModel(snapshot, snapshot_model));
        const S::TranslationContract reused = S::relationalToSmtContract(
            snapshot_model, false, S::ModelProjection{}, {}, &snapshot);
        VERIFY(reused.target_signature.symbols.front().name == "x");
        VERIFY(reused.target_signature.symbols.data() == snapshot.symbols.data());
        Diagnostics reusable_diags;
        VERIFY(reused.validate(reusable_diags));
        S::Assignment projected;
        VERIFY(reused.projection.project({{"x", "3"}, {"b", "true"}},
                                         projected, reusable_diags));
        VERIFY(projected.at("x") == "3" && projected.at("b") == "true");
        S::Signature source_edit = reused.source_signature.materialize();
        source_edit.symbols.front().name = "private-edit";
        VERIFY(reused.target_signature.symbols.front().name == "x");
        snapshot_model.decls.front().name = "renamed";
        VERIFY(!S::signatureMatchesModel(snapshot, snapshot_model));
        const S::TranslationContract rebuilt = S::relationalToSmtContract(
            snapshot_model, false, S::ModelProjection{}, {}, &snapshot);
        VERIFY(rebuilt.target_signature.symbols.front().name == "renamed");
        std::swap(snapshot_model.decls[0], snapshot_model.decls[1]);
        VERIFY(!S::signatureMatchesModel(snapshot, snapshot_model));
        const S::TranslationContract reordered = S::relationalToSmtContract(
            snapshot_model, false, S::ModelProjection{}, {}, &snapshot);
        VERIFY(reordered.target_signature.symbols.front().name == "b");
        H::ConstraintModel changed_sort_model = relationalExample();
        changed_sort_model.decls.front().sort = H::Sort::boolean();
        VERIFY(!S::signatureMatchesModel(snapshot, changed_sort_model));
        const S::TranslationContract changed_sort = S::relationalToSmtContract(
            changed_sort_model, false, S::ModelProjection{}, {}, &snapshot);
        VERIFY(changed_sort.target_signature.symbols.front().codomain.kind
               == H::SortKind::BOOL);

        S::SignatureSnapshot moved;
        {
            S::SignatureSnapshot source(S::signatureOf(snapshot_model));
            moved = std::move(source);
        }
        VERIFY(moved.symbols.front().name == "b");
        {
            S::SignatureSnapshot destination(std::move(moved));
            VERIFY(destination.symbols.front().name == "b");
        }
        VERIFY(moved.symbols.empty());
        VERIFY(moved.symbols.begin() == moved.symbols.end());

        H::ConstraintModel datatype_model;
        datatype_model.datatypes.push_back({
            "Tree", {}, {{"leaf", {{"label", H::Sort::integer()}}}}, {}, false});
        S::SignatureSnapshot datatype_signature(S::signatureOf(datatype_model));
        VERIFY(S::signatureMatchesModel(datatype_signature, datatype_model));
        datatype_model.datatypes.front().constructors.front().selectors.front().sort =
            H::Sort::boolean();
        VERIFY(!S::signatureMatchesModel(datatype_signature, datatype_model));

        H::ConstraintModel free_sort_model;
        free_sort_model.uninterpreted_sorts.push_back({"Color", 1, {}});
        S::SignatureSnapshot free_sort_signature(S::signatureOf(free_sort_model));
        VERIFY(S::signatureMatchesModel(free_sort_signature, free_sort_model));
        free_sort_model.uninterpreted_sorts.front().arity = 2;
        VERIFY(!S::signatureMatchesModel(free_sort_signature, free_sort_model));
    }

    {
        // Sharing an index must not turn same-named, same-typed overloads into
        // a unique mapping. The normal ambiguity check still rejects them.
        H::ConstraintModel empty_model;
        S::TranslationContract ambiguous =
            S::relationalToSmtContract(empty_model, false);
        S::Signature duplicate_symbols;
        duplicate_symbols.symbols.push_back(
            {"dup", S::SymbolKind::CONSTANT, {}, H::Sort::integer()});
        duplicate_symbols.symbols.push_back(
            {"dup", S::SymbolKind::CONSTANT, {}, H::Sort::integer()});
        S::SignatureSnapshot duplicates(std::move(duplicate_symbols));
        ambiguous.source_signature = duplicates;
        ambiguous.target_signature = duplicates;
        ambiguous.symbol_map.push_back({"dup", "dup"});
        ambiguous.sort_map.push_back({H::Sort::integer(), H::Sort::integer()});
        Diagnostics diags;
        VERIFY(!ambiguous.validate(diags));
        VERIFY(diags.hasErrors());
    }

    {
        // A name can denote several overloads. Each source overload must have
        // exactly one compatible target; ordering and storage sharing do not
        // change the ambiguity rule.
        H::ConstraintModel empty_model;
        auto overloaded = S::relationalToSmtContract(empty_model, false);
        S::Signature source;
        source.symbols = {
            {"z", S::SymbolKind::CONSTANT, {}, H::Sort::integer()},
            {"f", S::SymbolKind::FUNCTION, {H::Sort::integer()}, H::Sort::integer()},
            {"a", S::SymbolKind::CONSTANT, {}, H::Sort::boolean()},
            {"f", S::SymbolKind::FUNCTION, {H::Sort::boolean()}, H::Sort::boolean()}};
        S::Signature target;
        target.symbols.assign(source.symbols.rbegin(), source.symbols.rend());
        overloaded.source_signature = S::SignatureSnapshot(source);
        overloaded.target_signature = S::SignatureSnapshot(target);
        overloaded.symbol_map = {{"f", "f"}, {"z", "z"}, {"a", "a"}};
        overloaded.sort_map = {{H::Sort::integer(), H::Sort::integer()},
                               {H::Sort::boolean(), H::Sort::boolean()}};
        Diagnostics good;
        VERIFY(overloaded.validate(good));
        target.symbols.push_back(source.symbols[1]);
        overloaded.target_signature = S::SignatureSnapshot(target);
        Diagnostics duplicate;
        VERIFY(!overloaded.validate(duplicate));
        target.symbols.pop_back();
        target.symbols.erase(target.symbols.begin());
        overloaded.target_signature = S::SignatureSnapshot(target);
        Diagnostics missing_overload;
        VERIFY(!overloaded.validate(missing_overload));
        overloaded.target_signature = S::SignatureSnapshot(source);
        for (const std::string& missing : {std::string("0"), std::string("g"),
                                           std::string("zz")}) {
            auto unknown = overloaded;
            unknown.symbol_map[0].target = missing;
            Diagnostics diagnostics;
            VERIFY(!unknown.validate(diagnostics));
        }
    }

    {
        // SMT-LIB sort and term namespaces are distinct. It is legal and common
        // for a datatype sort and its constructor to share a spelling. Phi has
        // one textual mapping for that spelling and type/kind matching resolves
        // both symbols independently.
        H::ConstraintModel datatype_model;
        H::DatatypeDecl datatype;
        datatype.name = "List";
        datatype.constructors.push_back({"List", {}});
        datatype_model.datatypes.push_back(std::move(datatype));
        datatype_model.funs.push_back(
            {"Reach", {H::Sort::datatype("List")}, H::Sort::boolean(), {}});
        const S::TranslationContract contract = S::chcToRelationalContract(
            datatype_model, Fidelity::exact());
        Diagnostics diags;
        VERIFY(contract.validate(diags));
        VERIFY(!diags.hasErrors());
    }

    {
        S::TranslationPipeline inconsistent;
        inconsistent.add(S::miniZincToRelationalContract(model));
        S::TranslationContract target = S::relationalToSmtContract(model, true);
        target.source.satisfaction_relation = "a different relation with the same id";
        inconsistent.add(std::move(target));
        Diagnostics diags;
        VERIFY(!inconsistent.validate(diags));
        VERIFY(diags.hasErrors());
    }

    {
        // Emitting an optimization problem as plain SMT preserves feasibility,
        // but no longer preserves or orders optimum values.
        const S::TranslationContract feasibility =
            S::relationalToSmtContract(model, false);
        VERIFY(feasibility.target.id == "smt-lib");
        VERIFY(!feasibility.claimed_fidelity.preserves_optimum);
        VERIFY(feasibility.objectives.source == S::ObjectiveOrder::MINIMIZE);
        VERIFY(feasibility.objectives.target == S::ObjectiveOrder::SATISFACTION);
        VERIFY(feasibility.objectives.source_directions.size() == 1);
        VERIFY(feasibility.objectives.target_directions.empty());
        VERIFY(feasibility.objectives.value_map_id == "forget-objective");
        Diagnostics diags;
        VERIFY(feasibility.validate(diags));
        VERIFY(!diags.hasErrors());
    }

    {
        S::TranslationPipeline pipeline;
        pipeline.add(S::miniZincToRelationalContract(model));
        pipeline.add(S::relationalToSmtContract(
            model, true, pipeline.stages().back().projection));
        S::Assignment target{{"x", "4"}, {"b", "false"}, {"aux!0", "17"}};
        S::Assignment source;
        Diagnostics diags;
        VERIFY(pipeline.project(target, source, diags));
        VERIFY(source.size() == 2);
        VERIFY(source.at("x") == "4");
        VERIFY(source.at("b") == "false");
        VERIFY(source.count("aux!0") == 0);
    }

    {
        // Constants in a source-level output tuple are reconstructed without
        // asking the target solver for a value under a fake symbol name.
        S::ModelProjection projection;
        projection.observables.push_back(
            {"a[1]", "x", S::ProjectionKind::DIRECT});
        projection.observables.push_back(
            {"a[2]", "2", S::ProjectionKind::CONSTANT});
        S::Assignment source;
        Diagnostics diags;
        VERIFY(projection.project({{"x", "7"}}, source, diags));
        VERIFY(source.at("a[1]") == "7");
        VERIFY(source.at("a[2]") == "2");
    }

    {
        // Only beta's target coordinates must pass through the final stage.
        // Keep shared coordinates once, skip constants, and retain the full
        // signature and bound axioms even for an unobserved auxiliary.
        H::ConstraintModel projected_model = model;
        projected_model.decls.push_back(
            {"hidden", H::Sort::integer(), H::mkInt(-1), H::mkInt(1), {}});
        projected_model.decls.back().auxiliary = true;
        projected_model.funs.push_back(
            {"unused", {H::Sort::integer()}, H::Sort::boolean(), {}});
        S::ModelProjection required;
        required.observables.push_back({"left", "x", S::ProjectionKind::DIRECT});
        required.observables.push_back({"right", "x", S::ProjectionKind::DIRECT});
        required.observables.push_back({"fixed", "7", S::ProjectionKind::CONSTANT});
        required.choices.push_back({"action", {{"take", "b"}}});
        required.choices.push_back({"event", {{"method", "b"}}});
        const S::TranslationContract contract =
            S::relationalToSmtContract(projected_model, true, required);
        const S::TranslationContract complete =
            S::relationalToSmtContract(projected_model, true);
        VERIFY(contract.projection.observables.size() == 2);
        VERIFY(contract.source_signature.symbols.size() == complete.source_signature.symbols.size());
        VERIFY(contract.target_signature.symbols.size() == complete.target_signature.symbols.size());
        VERIFY(contract.target_axioms.size() == complete.target_axioms.size());
        VERIFY(contract.symbol_map.size() == complete.symbol_map.size());
        Diagnostics diags;
        VERIFY(contract.validate(diags));
        S::Assignment core, source;
        VERIFY(contract.projection.project({{"x", "4"}, {"b", "true"}}, core, diags));
        VERIFY(required.project(core, source, diags));
        VERIFY(source.at("left") == "4" && source.at("right") == "4");
        VERIFY(source.at("fixed") == "7");
        VERIFY(source.at("action") == "take" && source.at("event") == "method");

        S::ModelProjection constants;
        constants.observables.push_back({"fixed", "7", S::ProjectionKind::CONSTANT});
        VERIFY(S::relationalToSmtContract(projected_model, true, constants).projection.observables.empty());
        // An absent requested projection preserves the existing all-coordinate
        // API behavior, including relational auxiliary witnesses.
        const auto fallback = S::relationalToSmtContract(projected_model, true, S::ModelProjection{});
        VERIFY(fallback.projection.observables.size() == complete.projection.observables.size());
        VERIFY(fallback.projection.observables.size()
               == projected_model.decls.size() + projected_model.funs.size());
    }


    {
        S::ModelProjection projection;
        projection.choices.push_back(
            {"plan[0]", {{"pick(a)", "pick_a@0"}, {"drop(a)", "drop_a@0"}}});
        S::Assignment source;
        Diagnostics diags;
        VERIFY(projection.project(
            {{"pick_a@0", "1"}, {"drop_a@0", "false"}}, source, diags));
        VERIFY(source.at("plan[0]") == "pick(a)");
    }

    {
        // A grammar-only required projection must preserve just its selector
        // and hole coordinates; it must not take the direct-all shortcut.
        H::ConstraintModel grammar_model;
        grammar_model.decls.push_back({"grammar_sel", H::Sort::integer(), {}, {}, {}});
        grammar_model.decls.push_back({"grammar_hole", H::Sort::integer(), {}, {}, {}});
        grammar_model.decls.push_back({"unobserved_aux", H::Sort::integer(), {}, {}, {}});
        grammar_model.decls.back().auxiliary = true;
        S::ChoiceAlternative::Binding grammar_binding;
        grammar_binding.placeholder = "hole_token";
        grammar_binding.target_name = "grammar_hole";
        grammar_binding.kind = S::ChoiceAlternative::Binding::Kind::INTEGER;
        S::GrammarChoiceObservable grammar;
        grammar.source_name = "definition[grammar-only]";
        grammar.nodes.push_back({"grammar_sel", {
            {"hole_token", {}, {}, {grammar_binding}},
            {"0", {}, {}, {}},
        }});
        S::ModelProjection required;
        required.grammar_choices.push_back(grammar);
        const S::TranslationContract contract =
            S::relationalToSmtContract(grammar_model, false, required);
        VERIFY(contract.projection.observables.empty());
        VERIFY(contract.projection.optional_observables.size() == 2);
        Diagnostics diags;
        VERIFY(contract.validate(diags));
    }

    {
        // Selectorless/fixed grammar nodes still carry typed bindings. These
        // checks must run even though there is no selector to validate.
        const auto fixedBindingContract = [](
            const H::ConstraintModel& model, const std::string& target_name) {
            S::ChoiceAlternative::Binding binding;
            binding.placeholder = "fixed_hole_token";
            binding.target_name = target_name;
            binding.kind = S::ChoiceAlternative::Binding::Kind::INTEGER;
            S::GrammarChoiceObservable grammar;
            grammar.source_name = "fixed-definition";
            grammar.nodes.push_back({"", {
                {"fixed_hole_token", {}, {}, {binding}},
            }});
            S::ModelProjection required;
            required.grammar_choices.push_back(std::move(grammar));
            S::TranslationContract contract =
                S::relationalToSmtContract(model, false, required);
            // This overload composes target coordinates but does not copy
            // the source-side grammar witness projection into the result.
            contract.projection.grammar_choices = required.grammar_choices;
            return contract;
        };

        H::ConstraintModel unknown_model;
        S::TranslationContract unknown_contract =
            fixedBindingContract(unknown_model, "missing_fixed_hole");
        // Remove the derived optional projection so the only validation path
        // for this absent target is the fixed node's typed binding.
        unknown_contract.projection.optional_observables.clear();
        Diagnostics unknown_diags;
        VERIFY(!unknown_contract.validate(unknown_diags));
        VERIFY(std::any_of(unknown_diags.all().begin(), unknown_diags.all().end(),
                           [](const Diagnostic& diagnostic) {
                               return diagnostic.message.find(
                                   "grammar binding to unknown target symbol")
                                      != std::string::npos;
                           }));

        H::ConstraintModel wrong_sort_model;
        wrong_sort_model.decls.push_back(
            {"wrong_sort_hole", H::Sort::boolean(), {}, {}, {}});
        S::TranslationContract wrong_sort_contract =
            fixedBindingContract(wrong_sort_model, "wrong_sort_hole");
        wrong_sort_contract.projection.optional_observables.clear();
        Diagnostics wrong_sort_diags;
        VERIFY(!wrong_sort_contract.validate(wrong_sort_diags));
        VERIFY(std::any_of(wrong_sort_diags.all().begin(), wrong_sort_diags.all().end(),
                           [](const Diagnostic& diagnostic) {
                               return diagnostic.message.find(
                                   "grammar binding with the wrong target sort")
                                      != std::string::npos;
                           }));

        H::ConstraintModel valid_model;
        valid_model.decls.push_back(
            {"fixed_hole", H::Sort::integer(), {}, {}, {}});
        S::TranslationContract valid_contract =
            fixedBindingContract(valid_model, "fixed_hole");
        Diagnostics valid_diags;
        VERIFY(valid_contract.validate(valid_diags));
        S::Assignment projected;
        VERIFY(valid_contract.projection.project(
            {{"fixed_hole", "37"}}, projected, valid_diags));
        VERIFY(projected.at("fixed-definition") == "37");
    }

    {
        S::ModelProjection projection;
        projection.choices.push_back(
            {"plan[1]", {{"pick(a)", "pick_a@1"},
                         {"__padding_noop", "noop@1"}},
             "__padding_noop"});
        S::Assignment source;
        Diagnostics diags;
        VERIFY(projection.project(
            {{"pick_a@1", "false"}, {"noop@1", "true"}}, source, diags));
        VERIFY(source.empty());

        projection.choices[0].omit_label = "misspelled-noop";
        VERIFY(!projection.project(
            {{"pick_a@1", "false"}, {"noop@1", "true"}}, source, diags));
    }

    {
        // A bounded grammar circuit projects a full source witness, and only
        // demands selector values in the active derivation.
        S::GrammarChoiceObservable grammar;
        grammar.source_name = "definition[f]";
        grammar.prefix = "(define-fun f () Bool ";
        grammar.suffix = ")";
        grammar.root_node = 0;
        grammar.nodes.resize(2);
        grammar.nodes[0].selector_target = "root_choice";
        grammar.nodes[0].alternatives.push_back(
            {"(not child_token)", {"child_token"}, {1}, {}});
        grammar.nodes[0].alternatives.push_back({"true", {}, {}, {}});
        grammar.nodes[1].selector_target = "nested_choice";
        grammar.nodes[1].alternatives.push_back({"false", {}, {}, {}});
        grammar.nodes[1].alternatives.push_back({"true", {}, {}, {}});
        S::ModelProjection projection;
        projection.grammar_choices.push_back(grammar);
        S::Assignment source;
        Diagnostics diags;
        VERIFY(projection.project({{"root_choice", "1"}}, source, diags));
        VERIFY(source.at("definition[f]") == "(define-fun f () Bool true)");
        S::ModelProjection forward;
        forward.optional_observables.push_back(
            {"root_choice", "root_choice", S::ProjectionKind::DIRECT});
        forward.optional_observables.push_back(
            {"nested_choice", "nested_choice", S::ProjectionKind::DIRECT});
        S::Assignment forwarded;
        VERIFY(forward.project({{"root_choice", "1"}}, forwarded, diags));
        VERIFY(forwarded.size() == 1 && forwarded.at("root_choice") == "1");
        VERIFY(projection.project(forwarded, source, diags));
        VERIFY(source.at("definition[f]") == "(define-fun f () Bool true)");
        VERIFY(projection.project({{"root_choice", "0"},
                                   {"nested_choice", "1"}}, source, diags));
        VERIFY(source.at("definition[f]")
               == "(define-fun f () Bool (not true))");
        VERIFY(!projection.project({{"root_choice", "0"}}, source, diags));
        VERIFY(!projection.project({{"root_choice", "2"}}, source, diags));

        // A shared node is evaluated once and reused in the source tree.
        grammar.nodes[0].alternatives[0] =
            {"(= child_l child_r)", {"child_l", "child_r"}, {1, 1}, {}};
        projection.grammar_choices[0] = grammar;
        VERIFY(projection.project({{"root_choice", "0"},
                                   {"nested_choice", "1"}}, source, diags));
        VERIFY(source.at("definition[f]")
               == "(define-fun f () Bool (= true true))");

        // Cycles in the projection graph and ambiguous selector names are
        // rejected instead of looping or silently aliasing target values.
        grammar.nodes[1].alternatives[0] = {"again", {"again"}, {1}, {}};
        projection.grammar_choices[0] = grammar;
        VERIFY(!projection.project({{"root_choice", "1"}}, source, diags));
        grammar.nodes[1].selector_target = "root_choice";
        grammar.nodes[1].alternatives = {{"false", {}, {}, {}}};
        projection.grammar_choices[0] = grammar;
        VERIFY(!projection.project({{"root_choice", "1"}}, source, diags));

        S::GrammarChoiceObservable constants;
        constants.source_name = "definition[bv]";
        constants.prefix = "(define-fun bv () (_ BitVec 8) ";
        constants.suffix = ")";
        constants.nodes.push_back({"bv_select", {}});
        S::ChoiceAlternative::Binding binding;
        binding.placeholder = "bv_hole";
        binding.target_name = "bv_value";
        binding.kind = S::ChoiceAlternative::Binding::Kind::BITVECTOR;
        binding.bit_width = 8;
        constants.nodes[0].alternatives.push_back(
            {"bv_hole", {}, {}, {binding}});
        S::ModelProjection constant_projection;
        constant_projection.grammar_choices.push_back(constants);
        VERIFY(constant_projection.project(
            {{"bv_select", "0"}, {"bv_value", "#x0f"}}, source, diags));
        VERIFY(source.at("definition[bv]")
               == "(define-fun bv () (_ BitVec 8) #x0f)");
        VERIFY(!constant_projection.project(
            {{"bv_select", "0"}, {"bv_value", "#x1FF"}}, source, diags));

        S::GrammarChoiceObservable fixed;
        fixed.source_name = "fixed-definition";
        fixed.nodes.push_back({"", {{"true", {}, {}, {}}}});
        S::ModelProjection fixed_projection;
        fixed_projection.grammar_choices.push_back(fixed);
        VERIFY(fixed_projection.project({}, source, diags));
        VERIFY(source.at("fixed-definition") == "true");

        // Long unary derivations must project with space linear in the final
        // witness size and without recursive C++ call-stack growth.
        constexpr std::size_t chain_length = 12000;
        S::GrammarChoiceObservable deep;
        deep.source_name = "deep-definition";
        deep.prefix = "(define-fun deep () Bool ";
        deep.suffix = ")";
        deep.nodes.resize(chain_length);
        for (std::size_t i = 0; i + 1 < chain_length; ++i) {
            const std::string placeholder = "deep_child_" + std::to_string(i);
            deep.nodes[i].alternatives.push_back(
                {"(not " + placeholder + ")", {placeholder}, {i + 1}, {}});
        }
        deep.nodes.back().alternatives.push_back({"true", {}, {}, {}});
        S::ModelProjection deep_projection;
        deep_projection.grammar_choices.push_back(std::move(deep));
        VERIFY(deep_projection.project({}, source, diags));
        const std::string& deep_definition = source.at("deep-definition");
        std::string expected_deep = "(define-fun deep () Bool ";
        for (std::size_t i = 1; i < chain_length; ++i) {
            expected_deep += "(not ";
        }
        expected_deep += "true";
        expected_deep.append(chain_length - 1, ')');
        expected_deep += ")";
        VERIFY(deep_definition == expected_deep);
    }

    {
        S::ModelProjection projection;
        projection.observables.push_back(
            {"x", "x", S::ProjectionKind::DIRECT});
        const S::TranslationContract fzn = S::flatZincToRelationalContract(
            model, Fidelity::exact(), projection);
        const S::TranslationContract essence = S::essencePrimeToRelationalContract(
            model, Fidelity::exact(), projection);
        const S::TranslationContract xcsp = S::xcsp3ToRelationalContract(
            model, Fidelity::exact());
        Diagnostics diags;
        VERIFY(fzn.validate(diags));
        VERIFY(essence.validate(diags));
        VERIFY(xcsp.validate(diags));
        VERIFY(fzn.source.id == "flatzinc");
        VERIFY(essence.source.id == "essence-prime");
        VERIFY(xcsp.source.id == "xcsp3");
    }

    {
        // Custom planning signatures describe source states rather than every
        // grounded target coordinate. Target-only bounds must remain axioms,
        // and the two-stage beta map must still recover the source observable.
        H::ConstraintModel planning;
        planning.decls.push_back({"step_state", H::Sort::boolean(), {}, {}, {}});
        planning.decls.push_back(
            {"hidden_time", H::Sort::real(), H::mkReal("0"), H::mkReal("3"), {}});
        planning.decls.back().auxiliary = true;
        S::Signature source_signature;
        source_signature.symbols.push_back(
            {"source_state", S::SymbolKind::CONSTANT, {}, H::Sort::boolean()});
        S::ModelProjection projection;
        projection.observables.push_back(
            {"source_state", "step_state", S::ProjectionKind::DIRECT});
        const std::vector<S::SymbolMapping> mapping{{"source_state", "step_state"}};
        const std::vector<S::Sentence> extra_axioms{
            H::mkIdent("step_state", H::Sort::boolean())};
        for (bool hierarchical : {false, true}) {
            S::TranslationContract custom = hierarchical
                ? S::hddlToRelationalContract(planning, Fidelity::exact(), projection,
                                             source_signature, mapping, extra_axioms)
                : S::pddlToRelationalContract(planning, Fidelity::exact(), projection,
                                             source_signature, mapping, extra_axioms);
            VERIFY(custom.source_signature.symbols.size() == 1);
            VERIFY(custom.source_signature.symbols.front().name == "source_state");
            VERIFY(custom.target_signature.symbols.size() == 2);
            VERIFY(custom.symbol_map.size() == 1);
            VERIFY(custom.target_axioms.size() == 2);
            S::TranslationPipeline pipeline;
            pipeline.add(custom);
            pipeline.add(S::relationalToSmtContract(planning, false, projection));
            Diagnostics diagnostics;
            VERIFY(pipeline.validate(diagnostics));
            S::Assignment source;
            VERIFY(pipeline.project({{"step_state", "true"}}, source, diagnostics));
            VERIFY(source.size() == 1 && source.at("source_state") == "true");

            // Callers that omit custom source metadata retain identity maps.
            const auto fallback = hierarchical
                ? S::hddlToRelationalContract(planning, Fidelity::exact(), {})
                : S::pddlToRelationalContract(planning, Fidelity::exact(), {});
            Diagnostics fallback_diagnostics;
            VERIFY(fallback.validate(fallback_diagnostics));
            VERIFY(fallback.source_signature.symbols.size() == 1);
            VERIFY(fallback.source_signature.symbols.front().name == "step_state");
            VERIFY(fallback.target_axioms.size() == 1);
        }
    }

    {
        S::TranslationContract invalid;
        invalid.id = "invalid-exact-claim";
        invalid.source.id = "source";
        invalid.target.id = "target";
        Diagnostics diags;
        VERIFY(!invalid.validate(diags));
        VERIFY(diags.hasErrors());
    }

    std::cout << "All semantic-core tests passed." << std::endl;
    return 0;
}
