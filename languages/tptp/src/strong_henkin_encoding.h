#pragma once

#include "thf_expression_parser.h"

#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Lang::ThfPrototype {

/**
 * Strong, type-code Henkin encoding for monomorphic simple type theory.
 *
 * Unlike HenkinEncoding's convenient array-per-type prototype, this maps all
 * source values to one object carrier and all simple types to a recursive ADT.
 * A generic application function and universally quantified I/K/S/choice
 * axioms implement the polymorphic strong axiom without finite type-instance
 * sampling. Function domains are nonempty, disjoint by type, closed under
 * application and combinator denotation, and extensional.
 */
class StrongHenkinEncoding {
public:
    explicit StrongHenkinEncoding(Uir::Hir::ConstraintModel& model);

    /** Register all types, declare source constants, add strong axioms, and
     *  append every parsed formula to the target model. This operation is
     *  one-shot for an encoding instance. */
    void encode(const ThfFile& file);

    Uir::Hir::Sort objectSort() const;
    Uir::Hir::Sort typeCodeSort() const;
    Uir::Hir::ExprPtr typeCode(const Type& type) const;

private:
    using ExprPtr = Uir::Hir::ExprPtr;
    using Sort = Uir::Hir::Sort;

    void collectType(const Type& type);
    void collectTermTypes(const FunctionTermPtr& term);
    void declareEncodingSymbols();
    void addCoreAxioms();
    ExprPtr lowerFormula(const FunctionTermPtr& term,
                        std::unordered_map<std::uint64_t, ExprPtr>& scope);
    ExprPtr lowerObject(const FunctionTermPtr& term,
                        std::unordered_map<std::uint64_t, ExprPtr>& scope);
    ExprPtr lowerLambda(const FunctionTermPtr& term,
                        std::unordered_map<std::uint64_t, ExprPtr>& scope);
    ExprPtr hasType(ExprPtr value, const Type& type) const;
    ExprPtr app(ExprPtr function, ExprPtr argument) const;
    ExprPtr objectBoolean(ExprPtr formula) const;
    ExprPtr freshBound(const char* stem);
    std::string encodedName(const char* prefix, const std::string& source) const;
    std::string freshName(const char* prefix);
    void addConstraint(ExprPtr formula, const char* label,
                       Uir::SourceLoc source = {});

    Uir::Hir::ConstraintModel& model_;
    std::unordered_set<std::string> base_type_names_;
    std::unordered_map<std::string, std::string> base_constructors_;
    std::unordered_map<std::string, ExprPtr> source_symbols_;
    std::unordered_map<std::uint64_t, Type> binder_types_;
    Sort object_sort_;
    Sort type_code_sort_;
    std::string type_code_sort_name_;
    std::string arrow_constructor_name_;
    bool prepared_ = false;
    std::size_t fresh_ = 0;

    std::string has_type_name_;
    std::string app_name_;
    std::string is_true_name_;
    std::string not_name_;
    std::string and_name_;
    std::string or_name_;
    std::string implies_name_;
    std::string equality_name_;
    std::string forall_name_;
    std::string exists_name_;
    std::string true_name_;
    std::string false_name_;
    std::string identity_name_;
    std::string k_name_;
    std::string s_name_;
    std::string choice_name_;
    std::string true_object_name_;
    std::string false_object_name_;
};

} // namespace SOMTParser::Lang::ThfPrototype
