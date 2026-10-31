/* -*- Header -*-
 *
 * Feature — vocabulary for pass pre/post-conditions.
 *
 * An interned string rather than an enum: a new language introducing a new
 * high-level construct (MiniZinc's opt types, XCSP3's slide, CryptoLine's
 * modular assertions) must not force the core to be edited and rebuilt.
 * Comparison stays O(1) because the payload is an interned index.
 *
 * Contrast with Fidelity, which stays a closed struct because it takes part in
 * lattice operations that an open-ended domain would break.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_HIR_FEATURE_HEADER
#define SOMTPARSER_HIR_FEATURE_HEADER

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string_view>

namespace SOMTParser::Uir {

class Feature {
public:
    /** Intern @p name and return its handle. Thread-safe. */
    static Feature of(std::string_view name);

    /** Throws if @p id_ is out of range; the table is append-only and every
     *  Feature is minted by of(), so an out-of-range id means this object's
     *  own invariant is broken, not a normal runtime condition. */
    std::string_view name() const;

    bool operator==(Feature o) const noexcept { return id_ == o.id_; }
    bool operator!=(Feature o) const noexcept { return id_ != o.id_; }

    struct Hash {
        std::size_t operator()(Feature f) const noexcept {
            return std::hash<std::uint32_t>{}(f.id_);
        }
    };

private:
    explicit Feature(std::uint32_t id) noexcept : id_(id) {}
    std::uint32_t id_ = 0;
};

/** Features the core knows about. Languages and passes may mint more. */
namespace feat {
Feature comprehension();
Feature set();
Feature globalConstraint();
Feature reification();
Feature intVar();
Feature realVar();
Feature optionalVar();
Feature enumType();
Feature softConstraint();
Feature quantifier();
Feature nonlinear();
Feature transitionSystem();
Feature hornClause();
} // namespace feat

} // namespace SOMTParser::Uir

#endif /* SOMTPARSER_HIR_FEATURE_HEADER */
