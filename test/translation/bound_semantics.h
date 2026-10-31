/* -*- Header -*-
 *
 * Shared test helper: read the *meaning* of an emitted comparison assertion.
 *
 * Counting assertions cannot see the difference between "y >= 1 and y <= 9"
 * and "y <= 1 and y >= 9" -- the second makes the instance trivially UNSAT
 * while every count, every fidelity flag and every recorded Bound stays
 * identical. Swapping mkGe/mkLe in HirToParser::lower left the whole suite
 * green for exactly that reason.
 *
 * These helpers normalise a binary comparison node to the claim it makes about
 * one named variable, so a test can assert semantics instead of a count or a
 * printed string. Builders hash-cons, fold and may reorder arguments, so the
 * normalisation accepts the variable on either side and flips the relation
 * accordingly -- (>= y 1) and (<= 1 y) both normalise to "y >= 1".
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TEST_UIR_BOUND_SEMANTICS_H
#define SOMTPARSER_TEST_UIR_BOUND_SEMANTICS_H

#include "somtparser/ir/node.h"

#include <string>
#include <vector>

namespace test_bounds {

/** The relation, always read with the variable on the left. */
enum class Rel { GE, GT, LE, LT };

struct VarBound {
    Rel         rel = Rel::GE;
    std::string var;
    std::string constant;   // literal text of the numeric bound, e.g. "1", "-2147483648"
};

inline const char* relName(Rel r) {
    switch (r) {
    case Rel::GE: return ">=";
    case Rel::GT: return ">";
    case Rel::LE: return "<=";
    case Rel::LT: return "<";
    }
    return "?";
}

/** The same relation read from the other side: (<= 1 y) is (>= y 1). */
inline Rel flipRel(Rel r) {
    switch (r) {
    case Rel::GE: return Rel::LE;
    case Rel::GT: return Rel::LT;
    case Rel::LE: return Rel::GE;
    case Rel::LT: return Rel::GT;
    }
    return r;
}

/** Try to read @p n as "<var> <rel> <constant>".
 *  @return false when @p n is not a binary comparison between exactly one
 *  variable and one constant -- the caller decides whether that is a failure. */
inline bool readVarBound(SOMTParser::Node n, VarBound& out) {
    if (!n || SOMTParser::numChildren(n) != 2) {
        return false;
    }
    Rel rel;
    switch (SOMTParser::kind(n)) {
    case SOMTParser::NODE_KIND::NT_GE: rel = Rel::GE; break;
    case SOMTParser::NODE_KIND::NT_GT: rel = Rel::GT; break;
    case SOMTParser::NODE_KIND::NT_LE: rel = Rel::LE; break;
    case SOMTParser::NODE_KIND::NT_LT: rel = Rel::LT; break;
    default: return false;
    }
    SOMTParser::Node lhs = SOMTParser::child(n, 0);
    SOMTParser::Node rhs = SOMTParser::child(n, 1);
    if (!lhs || !rhs) {
        return false;
    }
    if (lhs->isVar() && rhs->isConst()) {
        out.rel = rel;
        out.var = lhs->getName();
        out.constant = rhs->getName();
        return true;
    }
    if (rhs->isVar() && lhs->isConst()) {
        out.rel = flipRel(rel);           // read from the variable's side
        out.var = rhs->getName();
        out.constant = lhs->getName();
        return true;
    }
    return false;
}

/** Every assertion in @p assertions that states a bound on a single variable. */
inline std::vector<VarBound> varBoundsOf(
        const std::vector<SOMTParser::Node>& assertions) {
    std::vector<VarBound> out;
    for (const auto& a : assertions) {
        VarBound b;
        if (readVarBound(a, b)) {
            out.push_back(b);
        }
    }
    return out;
}

/** Does @p assertions contain exactly one assertion meaning
 *  "@p var @p rel @p constant"? */
inline bool hasVarBound(const std::vector<SOMTParser::Node>& assertions,
                        const std::string& var, Rel rel,
                        const std::string& constant) {
    std::size_t found = 0;
    for (const auto& b : varBoundsOf(assertions)) {
        if (b.var == var && b.rel == rel && b.constant == constant) {
            ++found;
        }
    }
    return found == 1;
}

} // namespace test_bounds

#endif /* SOMTPARSER_TEST_UIR_BOUND_SEMANTICS_H */
