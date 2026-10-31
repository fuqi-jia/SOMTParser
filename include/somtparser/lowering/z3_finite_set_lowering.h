#ifndef SOMTPARSER_LOWERING_Z3_FINITE_SET_LOWERING_H
#define SOMTPARSER_LOWERING_Z3_FINITE_SET_LOWERING_H
#include <string>
namespace SOMTParser::Lower {
/** Rewrite typed SMT-LIB Set Int terms to Z3's Boolean-array representation.
 *  Cardinality requires exact finite support from constructors or unconditional
 *  interval constraints. Quantified uses must have proved finite carriers.
 *  Unsupported cases throw before any output is returned. Other solver
 *  dialects retain their native Set representation. */
std::string lowerFiniteSetsForZ3(const std::string& smt2);
/** Expand operations with proved finite support into exact store/select terms.
 *  The returned Boolean arrays must subsequently be encoded for OptiMathSAT.
 *  Unlike Z3 export, this never emits the nonstandard array-map operator. */
std::string lowerFiniteSetsForOptiMathSat(const std::string& smt2);
}
#endif
