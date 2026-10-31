/* -*- Header -*-
 *
 * Semantic configuration for translations between constraint languages.
 *
 * HIR describes executable constraints. This layer describes why translating
 * those constraints is valid: the source and target institutions, their
 * semantic assumptions, model projection, objective order, and the local proof
 * obligations carried by each pipeline stage.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_SEMANTICS_HEADER
#define SOMTPARSER_TRANSLATION_SEMANTICS_HEADER

#include "somtparser/translation/diagnostic.h"
#include "somtparser/translation/fidelity.h"
#include "somtparser/hir/hir.h"

#include <map>
#include <memory>
#include <mutex>
#include <cstddef>
#include <cstdint>
#include <string>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>

namespace SOMTParser::Uir::Sem {

// Compatibility name retained for clients that used the former Sem-scoped
// evidence enum. The canonical declaration now lives with Fidelity/CountEvidence.
using EvidenceKind = ::SOMTParser::Uir::EvidenceKind;

/** Cardinality and emptiness are independent semantic assumptions.
 *
 * A finite carrier may be empty or nonempty, while SMT-LIB sorts are
 * nonempty even when their cardinality is otherwise language dependent. */
enum class CarrierSemantics { FINITE, INFINITE, MIXED };
enum class CarrierEmptiness { NONEMPTY, EMPTY_ALLOWED, MIXED };
enum class FunctionSemantics { TOTAL, PARTIAL, MIXED };
enum class UndefinedSemantics { RELATIONAL_FALSE, KLEENE, STRICT, ERROR, TARGET_DEFINED };
enum class ArithmeticSemantics { NONE, INTEGER, RATIONAL, REAL, BIT_VECTOR, FLOATING_POINT, MIXED };
enum class OverflowSemantics { UNBOUNDED, MODULAR, ABORT, TARGET_DEFINED };
enum class DivisionSemantics { EUCLIDEAN, TRUNCATE_TOWARD_ZERO, FLOOR, EXACT_REAL, MIXED };
enum class ArraySemantics { FINITE_PARTIAL, TOTAL_EXTENSIONAL, FIXED_VECTOR, NONE };
enum class EqualitySemantics { EXTENSIONAL, INTENSIONAL, QUOTIENT, MIXED };
enum class QuantifierSemantics { FINITE_EXPANSION, NATIVE, MIXED, NONE };
enum class PhaseSemantics { STATIC_ERROR, CONSTRAINT_FAILURE, UNDEFINED_VALUE, MIXED };
enum class AnnotationSemantics { SEMANTIC, STRATEGY_ONLY, MIXED, NONE };

/** The semantic assumptions under which a language adapter is valid.
 *
 * Similar operator names do not imply similar semantics. In particular,
 * MiniZinc and SMT-LIB disagree about partial functions, arrays, division, and
 * the phase at which invalid fixed data is rejected. Keeping these choices in
 * one value lets a translation contract state its actual premises. */
struct AssumptionProfile {
    std::string             id;
    CarrierSemantics        carriers = CarrierSemantics::MIXED;
    CarrierEmptiness        carrier_emptiness = CarrierEmptiness::MIXED;
    FunctionSemantics       functions = FunctionSemantics::MIXED;
    UndefinedSemantics      undefined = UndefinedSemantics::TARGET_DEFINED;
    ArithmeticSemantics     arithmetic = ArithmeticSemantics::MIXED;
    OverflowSemantics       overflow = OverflowSemantics::TARGET_DEFINED;
    DivisionSemantics       division = DivisionSemantics::MIXED;
    ArraySemantics          arrays = ArraySemantics::NONE;
    EqualitySemantics       equality = EqualitySemantics::MIXED;
    QuantifierSemantics     quantifiers = QuantifierSemantics::MIXED;
    PhaseSemantics          invalid_phase = PhaseSemantics::MIXED;
    AnnotationSemantics     annotations = AnnotationSemantics::NONE;

    static AssumptionProfile miniZinc();
    static AssumptionProfile flatZinc();
    static AssumptionProfile essencePrime();
    static AssumptionProfile xcsp3();
    static AssumptionProfile typedRelationalCore();
    static AssumptionProfile smtLib();
    static AssumptionProfile omt();
};

/** Institution metadata. Sentence is Hir::ExprPtr and Model is Assignment in
 * this executable slice; a frontend may use a richer source model internally.
 * The names keep surface language, object logic, and meta logic distinct. */
struct Institution {
    std::string       id;
    std::string       surface_language;
    std::string       object_logic;
    std::string       meta_logic;
    std::string       sentence_space;
    std::string       model_class;
    std::string       satisfaction_relation;
    AssumptionProfile assumptions;
};

enum class SymbolKind { SORT, CONSTANT, FUNCTION, RELATION };

struct Symbol {
    std::string            name;
    SymbolKind             kind = SymbolKind::CONSTANT;
    std::vector<Hir::Sort> domain;
    Hir::Sort              codomain = Hir::Sort::boolean();
};

/** Explicit free sort constructors are separate from term symbols in SMT-LIB's
 *  sort/term namespaces. */
struct SortConstructor {
    std::string name;
    std::size_t arity = 0;
};

/** Compact contiguous family of symbols with a shared sort/signature.
 * Names are prefix + decimal(first + offset) + suffix, for 0 <= offset < count. */
struct SymbolPatternRange {
    std::string prefix;
    std::uint64_t first = 1;
    std::uint64_t count = 0;
    SymbolKind kind = SymbolKind::CONSTANT;
    std::vector<Hir::Sort> domain;
    Hir::Sort codomain = Hir::Sort::boolean();
    std::string suffix{};
    std::string name(std::uint64_t offset) const;
};

struct Signature {
    std::vector<Symbol> symbols;
    /** Explicit uninterpreted sort constructors; order preserves the source
     *  declaration order for faithful replay. */
    std::vector<SortConstructor> sort_constructors;
    /** Appended to preserve aggregate initialization of the original fields. */
    std::vector<SymbolPatternRange> symbol_ranges;
};

/** Immutable, cheaply copyable signature view retained by translation stages.
 *
 * Standalone Signature remains an ordinary mutable value. Contract snapshots
 * expose only const vector operations, so sharing cannot be invalidated by an
 * escaped mutable reference or iterator. `materialize()` makes an independent
 * mutable value when a caller needs to edit one. Constructing from an lvalue
 * copies it; constructing from an rvalue transfers its storage, so callers
 * must not retain and later mutate references or iterators into that value.
 */
template <class T>
class ReadOnlySignatureVector {
public:
    using Vector = std::vector<T>;
    using const_iterator = typename Vector::const_iterator;

    ReadOnlySignatureVector() = default;
    ReadOnlySignatureVector(const ReadOnlySignatureVector&) = default;
    ReadOnlySignatureVector(ReadOnlySignatureVector&& other) noexcept
        : owner_(std::move(other.owner_)),
          values_(std::exchange(other.values_, nullptr)),
          count_(std::exchange(other.count_, 0)),
          materialized_(std::move(other.materialized_)) {}

    std::size_t size() const noexcept { return values_ ? count_ : 0; }
    bool empty() const noexcept { return size() == 0; }
    const T* data() const noexcept { return values_ ? values_->data() : nullptr; }
    const T& operator[](std::size_t index) const { return (*values_)[index]; }
    const T& at(std::size_t index) const {
        if (index >= size()) { throw std::out_of_range("signature view index"); }
        return (*values_)[index];
    }
    const T& front() const { return values_->front(); }
    const T& back() const { return (*values_)[count_ - 1]; }
    operator const Vector&() const { return vector(); }
    const_iterator begin() const noexcept {
        return values_ ? values_->begin() : emptyVector().begin();
    }
    const_iterator end() const noexcept {
        return values_ ? values_->begin() + count_ : emptyVector().end();
    }
    const_iterator cbegin() const noexcept { return begin(); }
    const_iterator cend() const noexcept { return end(); }

private:
    friend struct SignatureSnapshot;

    ReadOnlySignatureVector& operator=(const ReadOnlySignatureVector&) = default;
    ReadOnlySignatureVector& operator=(ReadOnlySignatureVector&& other) noexcept {
        if (this != &other) {
            owner_ = std::move(other.owner_);
            values_ = std::exchange(other.values_, nullptr);
            count_ = std::exchange(other.count_, 0);
            materialized_ = std::move(other.materialized_);
        }
        return *this;
    }

    ReadOnlySignatureVector(std::shared_ptr<const Signature> owner,
                            const Vector* values)
        : owner_(std::move(owner)), values_(values), count_(values->size()) {}

    ReadOnlySignatureVector(std::shared_ptr<const Signature> owner,
                            const Vector* values, std::size_t count)
        : owner_(std::move(owner)), values_(values), count_(count),
          materialized_(count == values->size() ? nullptr
              : std::make_shared<MaterializedPrefix>()) {}

    const Vector& vector() const {
        if (!values_) { return emptyVector(); }
        if (!materialized_) { return *values_; }
        // Preserve the public const-vector conversion for callers that need
        // an owning contiguous vector. Ordinary iteration/indexing never
        // copies a prefix; copies of this immutable view share this lazy cache.
        std::call_once(materialized_->once, [this] {
            materialized_->values.assign(begin(), end());
        });
        return materialized_->values;
    }

    static const Vector& emptyVector() {
        static const Vector empty;
        return empty;
    }

    std::shared_ptr<const Signature> owner_;
    const Vector* values_ = nullptr;
    std::size_t count_ = 0;
    struct MaterializedPrefix {
        std::once_flag once;
        Vector values;
    };
    std::shared_ptr<MaterializedPrefix> materialized_;
};

struct SignatureSnapshot {
private:
    std::shared_ptr<const Signature> owner_;

public:
    ReadOnlySignatureVector<Symbol> symbols;
    ReadOnlySignatureVector<SymbolPatternRange> symbol_ranges;
    ReadOnlySignatureVector<SortConstructor> sort_constructors;
    std::uint64_t symbolCount() const noexcept;

    SignatureSnapshot() = default;
    explicit SignatureSnapshot(Signature value);
    SignatureSnapshot(const SignatureSnapshot&) = default;
    SignatureSnapshot(SignatureSnapshot&&) noexcept = default;
    SignatureSnapshot& operator=(const SignatureSnapshot& other);
    SignatureSnapshot& operator=(SignatureSnapshot&& other) noexcept;
    bool sharesStorageWith(const SignatureSnapshot& other) const noexcept {
        return owner_ == other.owner_
            && symbols.data() == other.symbols.data()
            && symbols.size() == other.symbols.size()
            && symbol_ranges.data() == other.symbol_ranges.data()
            && symbol_ranges.size() == other.symbol_ranges.size()
            && sort_constructors.data() == other.sort_constructors.data()
            && sort_constructors.size() == other.sort_constructors.size();
    }
    Signature materialize() const;
    /** Share an immutable leading symbol subsequence, keeping all sort and
     * generated-range declarations. Reject any count beyond this view. */
    SignatureSnapshot symbolPrefix(std::size_t count) const;
};

bool signatureMatchesModel(const SignatureSnapshot& signature,
                           const Hir::ConstraintModel& model);

Signature signatureOf(const Hir::ConstraintModel& model);

using Sentence = Hir::ExprPtr;
using Assignment = std::map<std::string, std::string>;

struct SymbolMapping {
    std::string source;
    std::string target;
};

struct SymbolRangeMapping {
    std::string source_prefix;
    std::string target_prefix;
    std::uint64_t source_first = 1;
    std::uint64_t target_first = 1;
    std::uint64_t count = 0;
    std::string source_suffix{};
    std::string target_suffix{};
};

/** Object-language sort component of Phi. It is explicit because symbol names
 * alone cannot validate an enum-to-Int or finite-set-to-bit-vector adapter. */
struct SortMapping {
    Hir::Sort source;
    Hir::Sort target;
};

enum class ProjectionKind { DIRECT, BOOL_FROM_ZERO_ONE, CONSTANT };

struct Observable {
    std::string    source_name;
    std::string    target_name;
    ProjectionKind projection = ProjectionKind::DIRECT;
};

/** Decode a source-level finite choice from one-hot target Booleans.
 *
 * Planning frontends use this for plan[k]: the SMT model contains one Boolean
 * per grounded action, while the source observable is the selected action
 * name. Exactly one alternative must be true. A generated padding choice may
 * be named by omit_label; beta validates it like every other alternative but
 * does not expose it as a source action. */
struct ChoiceAlternative {
    std::string label;
    std::string target_name;
    /** A typed target constant substituted for one complete SMT term token in
     *  label after this alternative is selected. Bindings make parametric
     *  source definitions executable without treating model text as SMT code. */
    struct Binding {
        // SMT_TERM stores a String whose contents must lex as exactly one
        // complete source SMT-LIB term; it is never accepted as an arbitrary
        // source fragment. SMT_STRING_VALUE stores a target String value whose
        // model literal is itself the exact source String term to substitute.
        enum class Kind { INTEGER, BOOLEAN, BITVECTOR, SMT_TERM, SMT_STRING_VALUE };

        std::string placeholder;
        std::string target_name;
        Kind        kind = Kind::INTEGER;
        // Required for BITVECTOR; zero for all other kinds. Appended so
        // existing three-field aggregate initializers keep their meaning.
        unsigned    bit_width = 0;
    };
    std::vector<Binding> bindings;
};

struct ChoiceObservable {
    std::string                    source_name;
    std::vector<ChoiceAlternative> alternatives;
    std::string                    omit_label;
};

/** One production at a bounded grammar occurrence. The label is an SMT-LIB
 * term template. Child placeholders are replaced with recursively selected
 * child terms, then typed bindings are instantiated as for ChoiceAlternative. */
struct GrammarChoiceAlternative {
    std::string label;
    std::vector<std::string> child_placeholders;
    std::vector<std::size_t> children;
    std::vector<ChoiceAlternative::Binding> bindings;
};

struct GrammarChoiceNode {
    /** Integer-valued target constant selecting an alternative by zero-based
     * index. Empty means the sole alternative is fixed. A node is inspected
     * only when reachable from the chosen root. */
    std::string selector_target;
    std::vector<GrammarChoiceAlternative> alternatives;
};

/** Reconstruct one complete source term from a finite, bounded derivation
 * circuit. `prefix + selected root term + suffix` is the source observable.
 * Nodes may be shared, but cycles and ambiguous selector names are invalid. */
struct GrammarChoiceObservable {
    std::string source_name;
    std::string prefix;
    std::string suffix{};
    std::vector<GrammarChoiceNode> nodes;
    std::size_t root_node = 0;
};

/** The executable beta map from a target assignment to source observables. */
struct ObservableRange {
    std::string source_prefix;
    std::string target_prefix;
    std::uint64_t source_first = 1;
    std::uint64_t target_first = 1;
    std::uint64_t count = 0;
    ProjectionKind projection = ProjectionKind::DIRECT;
    std::string source_suffix{};
    std::string target_suffix{};
};

struct ModelProjection {
    std::vector<Observable> observables;
    std::vector<ChoiceObservable> choices;
    std::vector<GrammarChoiceObservable> grammar_choices;
    /** Direct model coordinates that are forwarded when present. Used for
     * inactive grammar-circuit selectors/constants, whose values are not
     * needed to reconstruct the selected derivation. */
    std::vector<Observable> optional_observables;
    /** Direct identity ranges are kept compact; appended for aggregate ABI. */
    std::vector<ObservableRange> observable_ranges;

    bool project(const Assignment& target, Assignment& source,
                 Diagnostics& diags) const;
};

/** The question answered by a language instance, independently of its syntax. */
enum class DecisionKind {
    SATISFIABILITY,
    /** #models rather than ∃model. Distinct from SATISFIABILITY because an
     *  encoding can preserve one and destroy the other -- see
     *  `Fidelity::count_status`. */
    MODEL_COUNTING,
    OPTIMIZATION,
    QBF_TRUTH,
    HORN_SATISFIABILITY,
    VALIDITY,
    SAFETY,
    PROGRAM_VERIFICATION,
    REACHABILITY,
    PLAN_EXISTENCE,
    FUNCTION_SYNTHESIS,
    REACTIVE_REALIZABILITY,
};

/** Whether a positive target result denotes a positive or negative source result. */
enum class VerdictPolarity { PRESERVE, INVERT };

/** Result-level component of a translation.
 *
 * Sentence/model preservation alone is insufficient for refutation encodings:
 * TPTP validity and program verification deliberately map a positive source
 * result to target UNSAT. These fields make that inversion executable metadata
 * rather than a comment attached to the parser. */
struct DecisionMapping {
    DecisionKind    source = DecisionKind::SATISFIABILITY;
    DecisionKind    target = DecisionKind::SATISFIABILITY;
    VerdictPolarity polarity = VerdictPolarity::PRESERVE;
    std::string     target_sat_meaning;
    std::string     target_unsat_meaning;

    bool targetSatMeansSourceYes() const noexcept {
        return polarity == VerdictPolarity::PRESERVE;
    }
};

/** How a source institution relates to first-order SMT/OMT.
 *
 * This is language-level capability metadata, not a claim that every construct
 * is implemented. BOUNDED_UNDER_APPROXIMATION means a real source witness is
 * obtained when all listed bounds are respected, while a negative bounded
 * result is not a global source result. */
enum class SmtEmbeddingKind {
    DIRECT_REDUCTION,
    BOUNDED_UNDER_APPROXIMATION,
    NO_DIRECT_FIRST_ORDER_REDUCTION,
};

/** Public semantic configuration for a registered surface language.
 *
 * Unlike TranslationContract, this exists even when parsing must refuse an
 * instance. It therefore records the object logic and why an SMT target is or
 * is not legitimate before any AST/HIR translation is attempted. */
struct SourceSemanticSpec {
    Institution                       institution;
    /** Decision problems admitted by the surface language. The instance-level
     * TranslationContract selects one after parsing its solve/query command. */
    std::vector<DecisionKind>          decisions;
    SmtEmbeddingKind                  smt_embedding =
        SmtEmbeddingKind::NO_DIRECT_FIRST_ORDER_REDUCTION;
    std::vector<Fidelity::Bound::Kind> required_bounds;
    /** Additional bounds selected by the instance's decision problem. A
     * policy-state bound is not an action-trace horizon. */
    std::map<DecisionKind, std::vector<Fidelity::Bound::Kind>> decision_bounds;
    std::string                       rationale;

    bool valid() const noexcept {
        return !institution.id.empty() && !institution.object_logic.empty()
            && !institution.model_class.empty()
            && !institution.satisfaction_relation.empty()
            && !institution.assumptions.id.empty() && !decisions.empty()
            && !rationale.empty();
    }

    bool supports(DecisionKind decision) const noexcept;
};

/** Semantic configuration for every registered language id. Unknown ids
 * return an invalid (empty) specification. */
SourceSemanticSpec sourceSemanticSpec(const std::string& language_id);

enum class ObjectiveOrder {
    SATISFACTION,
    MINIMIZE,
    MAXIMIZE,
    LEXICOGRAPHIC,
    PARETO,
    BOX,
    MINMAX,
    MAXMIN,
};

ObjectiveOrder objectiveOrderOf(const Hir::ConstraintModel& model);
bool hasOptimization(const Hir::ConstraintModel& model);

struct ObjectiveMapping {
    ObjectiveOrder source = ObjectiveOrder::SATISFACTION;
    ObjectiveOrder target = ObjectiveOrder::SATISFACTION;
    std::vector<Hir::ObjKind> source_directions;
    std::vector<Hir::ObjKind> target_directions;
    std::string               value_map_id = "identity";
    bool            order_preserving = true;
    bool            order_reflecting = true;
};

enum class ProofObligationKind {
    SOUNDNESS, COMPLETENESS, OBJECTIVE, OBSERVABLES, MODEL_COUNT
};

struct ProofObligation {
    ProofObligationKind kind = ProofObligationKind::SOUNDNESS;
    EvidenceKind        evidence = EvidenceKind::PENDING;
    std::string         rationale;
    /** Concrete test, proof, or implementation artifact references. Count
     *  preservation requires at least one reference in addition to a rationale. */
    std::vector<std::string> evidence_refs{};

};

/** Exact numeric bounds on one constant in the immutable target signature.
 * The index refers to target_signature.symbols, never to the source signature
 * (which may omit auxiliary declarations). Endpoints stay immutable and shared.
 * This stores the same sentence as lower <= symbol <= upper without allocating
 * a separate identifier and Boolean expression per declaration. */
struct DeclarationBoundsAxiom {
    std::size_t target_symbol_index = 0;
    /** Retained identity makes a stale or reordered index detectable. */
    std::string target_name;
    Hir::ExprPtr lower_bound;
    Hir::ExprPtr upper_bound;
    SourceLoc loc;

    /** Expand one axiom for consumers that need a formula. Return null for an
     * invalid index, nonnumeric constant, absent endpoints or nonliteral bounds. */
    Sentence materialize(const SignatureSnapshot& target_signature) const;
};

/** One local translation T=(Phi,A,alpha,beta,h).
 *
 * symbol_map is Phi, target_axioms is A, the adapter implementation is alpha,
 * projection is beta, and objectives records h plus its order obligations. */
struct TranslationContract {
    std::string                id;
    /** Stable identifier of alpha, the executable sentence translation.
     * The source-language implementation remains in its frontend, but the
     * contract must name that implementation so an audit can connect emitted
     * constraints and test evidence to the claimed sentence map. */
    std::string                sentence_translation_id;
    Institution                source;
    Institution                target;
    /** Immutable snapshots. To edit, materialize a Signature, modify it, then
     * assign a new SignatureSnapshot; snapshots never expose mutable aliases. */
    SignatureSnapshot          source_signature;
    SignatureSnapshot          target_signature;
    std::vector<SortMapping>   sort_map;
    std::vector<SymbolMapping> symbol_map;
    std::vector<Sentence>      target_axioms;
    ModelProjection            projection;
    DecisionMapping            decision;
    ObjectiveMapping           objectives;
    Fidelity                   claimed_fidelity = Fidelity::exact();
    std::vector<ProofObligation> obligations;
    /** Compact identity/renamed symbol correspondences for generated ranges. */
    std::vector<SymbolRangeMapping> symbol_range_map;
    /** Finite conjunction of the bounds on every named member. These are
     * scalar declarations, not SMT arrays or quantified fresh symbols. */
    std::vector<Hir::ScalarVarRange> target_range_axioms;
    /** Additional members of A, represented compactly for packed numeric
     * models. Materialization is optional and does not change their semantics. */
    std::vector<DeclarationBoundsAxiom> target_declaration_bounds;

    bool validate(Diagnostics& diags) const;
};

/** Check that an instance-level first stage conforms to its language-level
 * semantic specification, including decision kind and mandatory bounds. */
bool validateSourceContract(const SourceSemanticSpec& specification,
                            const TranslationContract& contract,
                            Diagnostics& diags);

/** A compositional semantic account of the frontend and lowering stages. */
class TranslationPipeline {
public:
    void add(TranslationContract contract);
    bool validate(Diagnostics& diags) const;
    /** Compose beta maps in reverse stage order. The input is a final target
     * assignment; the output uses source-level observable names. */
    bool project(const Assignment& target, Assignment& source,
                 Diagnostics& diags) const;

    const std::vector<TranslationContract>& stages() const noexcept { return stages_; }
    Fidelity fidelity() const;
    /** Compose result polarity across all stages. */
    bool targetSatMeansSourceYes() const noexcept;

private:
    std::vector<TranslationContract> stages_;
};

/** An expression in a language with partial operations. When defined is false,
 * value is intentionally unconstrained and must not be observed. */
struct PartialExpr {
    Hir::ExprPtr defined;
    Hir::ExprPtr value;
};

/** Builds a typed relational core while presenting ExprPtr to existing parsers.
 *
 * value() propagates definedness through an ordinary value operation.
 * relation() closes a Boolean scope as `defined(args) and relation(args)`.
 * boolean() treats each Boolean operand as its own Boolean scope. */
class RelationalBuilder {
public:
    PartialExpr total(Hir::ExprPtr value) const;
    PartialExpr inspect(const Hir::ExprPtr& value) const;
    Hir::ExprPtr remember(PartialExpr expression);

    Hir::ExprPtr value(Hir::Op op, const std::vector<Hir::ExprPtr>& args,
                       SourceLoc loc = {}, Hir::ExprPtr domain = {});
    Hir::ExprPtr attach(Hir::ExprPtr raw, const std::vector<Hir::ExprPtr>& inputs,
                        Hir::ExprPtr domain = {});
    Hir::ExprPtr relation(Hir::ExprPtr raw_relation,
                          const std::vector<Hir::ExprPtr>& inputs,
                          Hir::ExprPtr domain = {});
    Hir::ExprPtr predicate(Hir::Op op, const std::vector<Hir::ExprPtr>& args,
                           SourceLoc loc = {}, Hir::ExprPtr domain = {});
    Hir::ExprPtr boolean(Hir::Op op, const std::vector<Hir::ExprPtr>& args,
                         SourceLoc loc = {});
    /** Lazy conditional: only the selected branch must be defined. */
    Hir::ExprPtr conditional(const Hir::ExprPtr& condition,
                             const Hir::ExprPtr& when_true,
                             const Hir::ExprPtr& when_false,
                             SourceLoc loc = {});
    /** Use the fallback only when the first expression is undefined.
     * This captures partiality; it does not assert the first operand's domain. */
    Hir::ExprPtr fallback(const Hir::ExprPtr& first,
                          const Hir::ExprPtr& otherwise,
                          SourceLoc loc = {});
    Hir::ExprPtr require(const Hir::ExprPtr& boolean_expression) const;

    static Hir::ExprPtr conjunction(std::vector<Hir::ExprPtr> terms,
                                    SourceLoc loc = {});

private:
    // A raw-address key can outlive a temporary expression. Reusing that
    // address would give a new, total expression the old definition predicate.
    // Own each partial expression for the lifetime of this builder.
    std::unordered_map<Hir::ExprPtr, Hir::ExprPtr> definitions_;
};

TranslationContract miniZincToRelationalContract(const Hir::ConstraintModel& model);
TranslationContract flatZincToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection);
TranslationContract essencePrimeToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection);
/** Optional declaration-aligned immutable identifier hints avoid duplicating
 * source variable leaves in bound axioms. Missing or incompatible hints fall
 * back to a fresh correctly typed identifier; they cannot alter an axiom. */
TranslationContract xcsp3ToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    const std::vector<Hir::ExprPtr>& declaration_terms = {});
/** Exact elaboration contracts for source languages whose HIR variables and
 * functions already are their source observables. Unsupported ids produce an
 * invalid contract and are therefore rejected by pipeline validation. */
TranslationContract directLanguageToRelationalContract(
    const Hir::ConstraintModel& model, std::string language_id,
    const Fidelity& frontend_fidelity);
TranslationContract cryptoLineToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection);
/** CHC predicates are source observables whose values are relation
 * interpretations. Their direct textual SMT model definitions are carried by
 * the same projection container as scalar values, but beta's semantic domain
 * is the whole relation, not one predicate application. */
TranslationContract chcToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity);
TranslationContract tptpToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    bool has_positive_conjecture, Signature source_signature = {},
    std::vector<SymbolMapping> symbol_map = {},
    std::vector<Sentence> target_axioms = {});
/** THF0 is translated to a first-order Henkin encoding, not the untyped
 *  relational projection used by the CNF/FOF frontend path. The source-to-HIR
 *  contract deliberately has no source assignment projection: this adapter
 *  preserves the TPTP SAT/validity decision through the strong encoding. */
TranslationContract tptpThfToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    bool has_positive_conjecture);
TranslationContract pddlToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection, Signature source_signature = {},
    std::vector<SymbolMapping> symbol_map = {},
    std::vector<Sentence> target_axioms = {},
    const std::string& policy_mode = {});
TranslationContract hddlToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection, Signature source_signature = {},
    std::vector<SymbolMapping> symbol_map = {},
    std::vector<Sentence> target_axioms = {});
TranslationContract sygusToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection, Signature source_signature = {},
    std::vector<SymbolMapping> symbol_map = {},
    std::vector<Sentence> target_axioms = {});
TranslationContract syntcompToRelationalContract(
    const Hir::ConstraintModel& model, const Fidelity& frontend_fidelity,
    ModelProjection projection, Signature source_signature = {},
    std::vector<SymbolMapping> symbol_map = {},
    std::vector<Sentence> target_axioms = {});
/** Append a checked core-to-core definitional extension when passes add
 * fresh acyclic auxiliary functions. Other signature changes are rejected;
 * an unchanged signature leaves the pipeline and snapshots untouched. */
bool extendRelationalWithDefinedHelpers(const Hir::ConstraintModel& model,
                                       const std::string& pass_pipeline,
                                       TranslationPipeline& pipeline,
                                       Diagnostics& diagnostics);
TranslationContract relationalToSmtContract(const Hir::ConstraintModel& model,
                                             bool optimization_target);
TranslationContract relationalToSmtContract(const Hir::ConstraintModel& model,
                                             bool optimization_target,
                                             const ModelProjection& required_observables);
/** Reuse exact immutable post-pass signature and bound-axiom snapshots from
 * the preceding stage. Both hints are checked against the current post-pass
 * model; any mismatch falls back to independently constructed contract data. */
TranslationContract relationalToSmtContract(
    const Hir::ConstraintModel& model, bool optimization_target,
    const ModelProjection& required_observables,
    const std::vector<Hir::ExprPtr>& bound_axiom_hints,
    const SignatureSnapshot* postpass_signature_hint = nullptr);

} // namespace SOMTParser::Uir::Sem

#endif /* SOMTPARSER_TRANSLATION_SEMANTICS_HEADER */
