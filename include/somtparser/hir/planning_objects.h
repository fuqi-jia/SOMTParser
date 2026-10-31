#ifndef SOMTPARSER_HIR_PLANNING_OBJECTS_HEADER
#define SOMTPARSER_HIR_PLANNING_OBJECTS_HEADER

#include "somtparser/hir/hir.h"
#include "somtparser/hir/planning_numeric.h"
#include <optional>

namespace SOMTParser::Uir::Hir::Planning {

// A finite, named universe. Object i has integer code i+1; code 0 is the
// canonical payload of undefined, never an object and never a source term.
struct ObjectTypeDeclaration { std::string name; std::vector<std::string> parents; };
struct PlanningObject { std::string name; std::string type; };
struct ObjectUniverse {
    std::vector<ObjectTypeDeclaration> types; // implicit root "object"; acyclic
    std::vector<PlanningObject> objects;       // constants and problem objects
};
struct ObjectType { std::vector<std::string> alternatives; }; // finite union (either ...)
bool validateObjectUniverse(const ObjectUniverse&, Diagnostics&);
std::optional<bool> objectSubtype(const ObjectUniverse&, const ObjectType& actual,
                                  const ObjectType& expected, Diagnostics&);
std::optional<std::vector<std::size_t>> objectCarrier(const ObjectUniverse&, const ObjectType&, Diagnostics&);

struct ObjectStateCell { ExprPtr value; ExprPtr defined; ObjectType type; };
struct ObjectReadAccess { std::size_t cell; ExprPtr when; };
struct ObjectValue {
    ExprPtr value;                         // Int code
    ExprPtr defined;                       // Bool, kept separate from equality
    ObjectType type;
    std::vector<ObjectReadAccess> reads;    // dynamic reads, including address terms
    std::vector<ExprPtr> constraints;       // append ALL to the consuming model
};
struct ObjectCondition {
    ExprPtr value;
    ExprPtr defined;
    std::vector<ObjectReadAccess> reads;
    std::vector<ExprPtr> constraints;
};
// This is an explicit mathematical contract, not a claim that preliminary
// PDDL3.1 settled unknown values or temporal interference. STRICT propagates
// undefined through NOT/OR. ATOMIC_FALSE totalizes each atom before connectives.
enum class ObjectUndefinedPolicy { STRICT, ATOMIC_FALSE };
enum class ObjectAssignmentPolicy { SINGLE_WRITER, AGREEING_WRITERS };

std::optional<ObjectValue> objectConstant(const ObjectUniverse&, const std::string& name, Diagnostics&);
std::optional<ObjectValue> objectRead(const ObjectUniverse&, const ObjectStateCell&,
                                     std::size_t index, Diagnostics&);
std::optional<ObjectCondition> objectEqual(const ObjectUniverse&, const ObjectValue&, const ObjectValue&,
                                          ObjectUndefinedPolicy, Diagnostics&);
std::optional<ObjectCondition> objectLogical(Op, const std::vector<ObjectCondition>&, Diagnostics&);
ExprPtr objectSatisfied(const ObjectCondition&);

// Rows contain OBJECT INDICES (codes minus one). Every tuple of the declared
// parameter carriers must occur exactly once; ordering has no semantic meaning.
// Completeness is checked even when an argument is undefined or a carrier empty.
struct ObjectTable { std::vector<ObjectType> parameters; std::vector<std::vector<std::size_t>> rows; };
struct ObjectDispatch {
    ExprPtr defined;
    std::vector<ExprPtr> matches; // argument-definedness AND exact tuple equality
    std::vector<ObjectReadAccess> reads;
    std::vector<ExprPtr> constraints;
};
std::optional<ObjectDispatch> objectDispatch(const ConstraintModel&, const ObjectUniverse&,
    const ObjectTable&, const std::vector<ObjectValue>& arguments, Diagnostics&);
std::optional<ObjectValue> objectLookup(const ConstraintModel&, const ObjectUniverse&,
    const ObjectTable&, const std::vector<ObjectValue>& arguments,
    const std::vector<ObjectValue>& row_values, const ObjectType& result_type, Diagnostics&);
std::optional<ObjectCondition> objectPredicate(const ConstraintModel&, const ObjectUniverse&,
    const ObjectTable&, const std::vector<ObjectValue>& arguments,
    const std::vector<ExprPtr>& row_values, ObjectUndefinedPolicy, Diagnostics&);
// Numeric reads remain in NumericValue::reads. Object reads/obligations are
// separate, so equal indices in the two state spaces cannot accidentally alias.
struct ObjectNumericValue {
    NumericValue numeric;
    std::vector<ObjectReadAccess> object_reads;
    std::vector<ObjectReadAccess> numeric_reads; // same struct, numeric-state index space
    std::vector<ExprPtr> constraints;
};
std::optional<ObjectNumericValue> objectNumericLookup(const ConstraintModel&, const ObjectUniverse&,
    const ObjectTable&, const std::vector<ObjectValue>& arguments,
    const std::vector<NumericValue>& row_values, Diagnostics&);

struct ObjectAddress {
    ExprPtr defined;
    std::vector<std::size_t> cells;
    std::vector<ExprPtr> matches;
    std::vector<ObjectReadAccess> reads;
    std::vector<ExprPtr> constraints;
};
std::optional<ObjectAddress> objectAddress(const ConstraintModel&, const ObjectUniverse&,
    const ObjectTable&, const std::vector<ObjectValue>& arguments,
    const std::vector<std::size_t>& row_cells, Diagnostics&);
struct ObjectUpdate {
    ObjectAddress target;
    std::optional<ObjectValue> rhs; // nullopt means EXPLICIT assign undefined
    ExprPtr guard;                 // total firing condition; caller checks guard definedness
};
struct ObjectTransition { std::vector<ExprPtr> constraints; };
// All addresses/RHS/guards use BEFORE. A reachable define-fun cannot hide an
// AFTER read. Conflicts are evaluated after dynamic alias resolution. No
// concurrency/no-moving-target policy is silently imposed by this transition.
std::optional<ObjectTransition> buildObjectTransition(const ConstraintModel&, const ObjectUniverse&,
    const std::vector<ObjectStateCell>& before, const std::vector<ObjectStateCell>& after,
    const std::vector<ObjectUpdate>&, ObjectAssignmentPolicy, Diagnostics&);
// Initial values are object indices. Omitted cells are undefined. Repeated
// initialization, wrong types and out-of-range cells/objects are errors.
std::optional<ObjectTransition> initialObjectState(const ConstraintModel&, const ObjectUniverse&,
    const std::vector<ObjectStateCell>&, const std::vector<std::pair<std::size_t,std::size_t>>& values,
    Diagnostics&);

} // namespace SOMTParser::Uir::Hir::Planning
#endif
