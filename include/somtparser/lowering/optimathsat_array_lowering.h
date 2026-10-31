#ifndef SOMTPARSER_LOWERING_OPTIMATHSAT_ARRAY_LOWERING_H
#define SOMTPARSER_LOWERING_OPTIMATHSAT_ARRAY_LOWERING_H

#include <string>

namespace SOMTParser {
class Parser;
namespace Lower {

/** Whether a parser owns an Array sort with a Boolean index or element.
 *  The sort arena is inspected without traversing (potentially huge) formulas. */
bool needsOptiMathSatArrayLowering(const Parser& parser);
/** Retained acyclic recursive definitions need ordinary macro syntax in OMS. */
bool needsOptiMathSatDefinitionLowering(const Parser& parser);
/** Native Set sorts require finite-set lowering before the Bool-array pass. */
bool needsOptiMathSatSetLowering(const Parser& parser);

/** Encode Boolean array coordinates with the bijection false <-> #b0,
 *  true <-> #b1. Scalars remain Boolean; select/store/constant arrays insert
 *  the conversions at the array boundary. Nested arrays, scoped lets and
 *  function signatures retain their types. No domain axioms or quantifiers
 *  are introduced, so extensional array equality is preserved exactly.
 *  Parsing, scope handling and output all use explicit stacks. */
std::string lowerBooleanArraysForOptiMathSat(const std::string& smt2);

} // namespace Lower
} // namespace SOMTParser
#endif
