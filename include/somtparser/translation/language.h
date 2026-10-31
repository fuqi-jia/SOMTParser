/* -*- Header -*-
 *
 * Language — the frontend interface.
 *
 * A frontend's product is HIR. It may borrow the existing SMT-LIB parser
 * internally (CHC and the SMT-LIB baseline necessarily do), but it must lift
 * the result to HIR rather than putting DAGNode into a ParseOutcome. Otherwise
 * encoding decisions leak back into twenty-two separate frontends and the pass
 * pipeline stops being the single place they are made.
 *
 * parse() returns errors; it never lets an exception escape. Detection needs
 * content sniffing because extension alone is ambiguous: CHC-COMP files are
 * .smt2, exactly like plain SMT-LIB.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_LANGUAGE_HEADER
#define SOMTPARSER_TRANSLATION_LANGUAGE_HEADER

#include "somtparser/translation/diagnostic.h"
#include "somtparser/hir/hir.h"
#include "somtparser/translation/profile.h"
#include "somtparser/translation/report.h"
#include "somtparser/translation/semantics.h"

#include <cstddef>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

namespace SOMTParser::Lang {

struct ModuleOutcome;

/** Multiple files are a requirement, not a convenience: MiniZinc pairs .mzn
 *  with .dzn, MPS pairs a model with a basis. */
struct SourceUnit {
    std::string              main_path;                 // "-" means stdin
    std::vector<std::string> data_paths;
    std::string              inline_source;             // takes precedence when non-empty
    std::string              display_name = "<memory>";
};

struct ParseOptions {
    bool          strict = false;
    Uir::ParamMap options;
};

struct ParseOutcome {
    Uir::Hir::ConstraintModelPtr model;        // nullptr on failure
    Uir::Diagnostics   diagnostics;

    /** Local semantic contracts already discharged by the frontend. Empty for
     * frontends that have not migrated to the public semantic pivot yet. */
    Uir::Sem::TranslationPipeline semantics;

    /** Where a frontend records the encoding decisions it made.
     *
     *  A frontend chooses things no later stage can see it choosing: which of
     *  three admissible readings of an MPS bound to take, whether a WBO
     *  threshold is vacuous, that a TPTP conjecture was negated and so this
     *  script's UNSAT means the opposite of every other language's. Before this
     *  field those decisions could only be a warning or a source comment, and
     *  per-instance recorded fidelity -- the whole point of the report -- was
     *  unavailable at the layer that makes most of the decisions.
     *
     *  Write only choices and warnings; translate() owns the rest and
     *  TranslationReport::mergeFrontend refuses a report that touches them. */
    Uir::TranslationReport report;

    // Symbol-free response requests after the final query. They are script
    // protocol metadata, not HIR constraints, and survive lowering separately.
    std::vector<std::string> terminal_responses;

    bool ok() const noexcept { return static_cast<bool>(model); }
};

/** Which unified ops this language claims to support. Feeds the coverage table. */
struct OpCoverage {
    std::size_t              supported = 0;
    std::size_t              total = 0;
    std::vector<std::string> missing;
};

class Language {
public:
    virtual ~Language() = default;

    virtual std::string id() const = 0;             // stable, e.g. "minizinc"
    virtual std::string displayName() const = 0;
    virtual std::string version() const = 0;
    virtual std::vector<std::string> extensions() const = 0;

    /** Confidence in [0,1] that this content belongs to this language.
     *  Only consulted when an extension has more than one claimant. */
    virtual double sniff(std::string_view head) const { (void)head; return 0.0; }

    virtual const OpCoverage& coverage() const = 0;

    /** Does this language consume SourceUnit::data_paths?
     *
     *  Defaults to false, and translate() refuses a unit that carries data
     *  paths a language does not claim, so a frontend that forgets to override
     *  this fails loudly rather than silently discarding the data file and
     *  reporting success on a model it never read. Override to true only once
     *  parse() actually reads them. */
    virtual bool acceptsDataFiles() const { return false; }

    /** The single entry point. Implementations must catch every exception and
     *  turn it into a diagnostic. */
    virtual ParseOutcome parse(const SourceUnit& unit, const ParseOptions& opts) = 0;

    /** Import a typed library or an open model, without inventing a query or
     * resolving an external relation. Unsupported by default. */
    virtual ModuleOutcome parseModule(const SourceUnit& unit);
    /** Frontend reader choices for module imports. The default rejects all
     * options instead of silently ignoring a requested source interpretation. */
    virtual ModuleOutcome parseModule(const SourceUnit& unit, const ParseOptions& opts);
};

using LanguagePtr = std::shared_ptr<Language>;

class LanguageRegistry {
public:
    static LanguageRegistry& instance();

    void  add(LanguagePtr lang);
    Language* byId(std::string_view id) const;

    /** Extension narrows the candidates; sniff() breaks a tie. Returns nullptr
     *  when nothing claims the input rather than guessing. */
    Language* detect(const SourceUnit& unit) const;

    std::vector<Language*> all() const;

    /** First @p max_bytes of a file, for sniffing. Empty on any I/O error. */
    static std::string readHead(const std::string& path, std::size_t max_bytes = 8192);

private:
    std::vector<LanguagePtr> langs_;
};

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_TRANSLATION_LANGUAGE_HEADER */
