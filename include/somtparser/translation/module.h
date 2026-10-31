/* Typed source artifacts that do not denote a closed satisfiability query. */
#ifndef SOMTPARSER_TRANSLATION_MODULE_HEADER
#define SOMTPARSER_TRANSLATION_MODULE_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

struct StateVariable {
    std::string current, next, role; // input, output, or local
    Uir::Hir::Sort sort;
};

struct TransitionSystem {
    std::string name;
    std::vector<StateVariable> variables;
    // Declarations for both states and rigid symbols. Relations are separate:
    // conjoining init/trans/invariant here would invent a verification task.
    Uir::Hir::ConstraintModel context;
    Uir::Hir::ExprPtr init, trans, invariant;
    std::vector<Uir::Hir::ExprPtr> outputs, bad;
};

struct ExternalArgument {
    Uir::Hir::Sort sort;
    bool array = false;
    bool parameter = false;
    std::vector<Uir::Hir::ExprPtr> values; // scalar has exactly one value
};

struct ExternalCall {
    std::string predicate;
    std::vector<ExternalArgument> arguments;
    // Preserve the full annotation spelling, including callback filenames and
    // arguments. Import never executes a program or loads a shared library.
    std::string annotations;
    Uir::SourceLoc loc;
};

struct SourceModule {
    std::string language;
    std::vector<TransitionSystem> systems;
    // In an open FlatZinc model these are ONLY the known constraints. This is
    // deliberately not a Translation and cannot be passed to solve/read.
    Uir::Hir::ConstraintModel known;
    std::vector<ExternalCall> unresolved;
    struct SourceRewrite {
        std::string rule, original, replacement;
        Uir::SourceLoc loc;
    };
    // Explicit source dialect normalization, retained in the export interface.
    std::vector<SourceRewrite> source_rewrites;
};

struct ModuleOutcome {
    std::shared_ptr<const SourceModule> module;
    Uir::Diagnostics diagnostics;
    bool ok() const noexcept { return module && !diagnostics.hasErrors(); }
};

ModuleOutcome importModule(const SourceUnit& unit, const std::string& language = "",
                           const ParseOptions& opts = {});
bool validateModule(const SourceModule& module, Uir::Diagnostics& diagnostics);
bool readModuleSource(const SourceUnit& unit, std::string& source,
                      Uir::Diagnostics& diagnostics);

struct ModuleExport {
    std::string smt2;
    // JSON interface: exported relation names/parameters and external linkage.
    std::string interface_json;
    Uir::Diagnostics diagnostics;
    bool ok() const noexcept { return !smt2.empty() && !diagnostics.hasErrors(); }
};

/** Export a library or open model, retaining every relation and external call.
 * No check-sat or exit is emitted. External declarations require interpretation
 * by the consumer; exporting them does not implement a callback. */
ModuleExport exportModule(const SourceModule& module);

} // namespace SOMTParser::Lang
#endif
