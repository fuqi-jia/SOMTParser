#pragma once

#include "somtparser/hir/hir.h"

#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang::ThfPrototype {

/** Monomorphic simple type. Arrow is right-associative: arrow(A, arrow(B,C)). */
struct Type {
    enum class Kind { BOOL, INT, REAL, INDIVIDUAL, ARROW } kind = Kind::BOOL;
    std::string name;
    std::shared_ptr<const Type> domain;
    std::shared_ptr<const Type> codomain;

    static Type boolean();
    static Type integer();
    static Type real();
    static Type individual(std::string name = "$i");
    static Type arrow(Type domain, Type codomain);
    bool isArrow() const { return kind == Kind::ARROW; }
};

struct TypedBinder {
    std::string name;
    Type type;
};

/**
 * Henkin-domain encoding infrastructure for monomorphic simple types.
 *
 * Arrow values are HIR arrays, but source quantifiers are guarded by a
 * type-specific domain predicate. `ensureType` adds non-emptiness, closure,
 * and extensional-representative axioms once for each encountered arrow type.
 * The source equality relation is recursively extensional and never relies on
 * raw SMT array equality except in the representative uniqueness axiom.
 *
 * IMPORTANT: this does not yet axiomatize closure under every lambda-definable
 * function for infinite/uninterpreted carriers, so `quantify` rejects those
 * arrow types. Finite Boolean-generated types use the full finite array space,
 * whose values are all lambda-definable. Do not treat membership guards by
 * themselves as complete higher-order quantification.
 */
class HenkinEncoding {
public:
    explicit HenkinEncoding(Uir::Hir::ConstraintModel& model);

    /** Reserve source identifiers before lowering so generated symbols cannot shadow them. */
    void reserveSourceNames(const std::vector<std::string>& names);

    Uir::Hir::Sort sortOf(const Type& type);
    /** Declare one source value; arrow values receive a Henkin-domain axiom. */
    Uir::Hir::ExprPtr declareValue(std::string source_name, const Type& type,
                                  bool auxiliary = false);
    Uir::Hir::ExprPtr member(const Type& type, Uir::Hir::ExprPtr value);
    Uir::Hir::ExprPtr apply(const Type& function_type,
                            Uir::Hir::ExprPtr function,
                            Uir::Hir::ExprPtr argument);
    Uir::Hir::ExprPtr equal(const Type& type,
                           Uir::Hir::ExprPtr left,
                           Uir::Hir::ExprPtr right);
    /**
     * Materialize the two logical constant functions `^x.$false` and
     * `^x.$true` at A -> Bool. This is a necessary Henkin-closure axiom
     * family, but not by itself sufficient to admit arbitrary function
     * quantification.
     */
    void ensureBooleanConstantLambdas(const Type& domain);
    /** Arrow quantification is admitted only for finite Boolean-generated types. */
    Uir::Hir::ExprPtr quantify(bool universal, const TypedBinder& binder,
                               Uir::Hir::ExprPtr body);

    /** Add a closed lambda value `^arg. body` as an auxiliary array and return it. */
    Uir::Hir::ExprPtr lambda(std::string target_name, const TypedBinder& argument,
                             const Type& result_type, Uir::Hir::ExprPtr body);

    /**
     * Add a lambda whose free variables are exactly `captures`. When captures
     * are nonempty, a target-only helper function maps their values to the
     * array representing the lambda; the returned value is that helper applied
     * to `capture_values`. Both lists must have matching lengths and sorts.
     */
    Uir::Hir::ExprPtr lambda(std::string target_name,
                             const std::vector<TypedBinder>& captures,
                             const std::vector<Uir::Hir::ExprPtr>& capture_values,
                             const TypedBinder& argument,
                             const Type& result_type,
                             Uir::Hir::ExprPtr body);

private:
    std::string key(const Type& type) const;
    std::string domainName(const Type& type);
    bool hasFullFiniteDomain(const Type& type) const;
    Uir::Hir::ExprPtr rawMember(const Type& type, Uir::Hir::ExprPtr value);
    void ensureType(const Type& type);
    void addArrowAxioms(const Type& type);
    void addConstraint(Uir::Hir::ExprPtr formula, const std::string& label);

    Uir::Hir::ConstraintModel& model_;
    std::unordered_map<std::string, bool> emitted_;
    std::unordered_map<std::string, std::string> domain_names_;
    std::unordered_set<std::string> boolean_constant_closures_;
    std::unordered_set<std::string> reserved_names_;
    std::size_t fresh_ = 0;
};

} // namespace SOMTParser::Lang::ThfPrototype
