/* Internal classical-planning service shared by the PDDL and HDDL frontends. */

#ifndef SOMTPARSER_LANGUAGES_PDDL_INTERNAL_HEADER
#define SOMTPARSER_LANGUAGES_PDDL_INTERNAL_HEADER

#include "somtparser/translation/diagnostic.h"
#include "somtparser/hir/hir.h"
#include "somtparser/translation/language.h"
#include "somtparser/translation/report.h"
#include "somtparser/translation/semantics.h"

#include <string>
#include <map>
#include <vector>

namespace SOMTParser::Lang::PddlInternal {

using ActionInstances = std::map<std::string, std::vector<std::vector<std::string>>>;

struct ClassicalEncoding {
    Uir::Hir::ConstraintModelPtr  model;
    Uir::Sem::ModelProjection     projection;
    Uir::Sem::Signature           source_signature;
    std::vector<Uir::Sem::SymbolMapping> symbol_map;
    std::vector<Uir::Sem::Sentence>      target_axioms;
};

/** Build the accepted deterministic classical/ADL PDDL fragment from in-memory
 * domain/problem texts. HDDL uses this only after it has independently parsed
 * and validated the hierarchy, then adds the decomposition language over the
 * returned action-choice coordinates. `multiple_inheritance` is selected only
 * by the IPC HDDL dialect; it retains every parent edge of a repeated type
 * declaration. Standalone PDDL keeps its existing declaration strictness. */
ClassicalEncoding buildClassicalEncoding(
    const std::string& domain, const std::string& problem,
    const std::string& display_name, unsigned horizon,
    Uir::Diagnostics& diagnostics, Uir::TranslationReport& report,
    bool lenient_requirements = false,
    const ActionInstances* allowed_actions = nullptr,
    bool multiple_inheritance = false);

/** Read `lenient_requirements` from a frontend's options.
 *
 *  Shared so PDDL and HDDL cannot disagree about what the flag is called or
 *  what counts as on: they parse the same files with the same checker, and an
 *  option spelt two ways is an option one of them silently ignores. */
bool lenientRequirements(const Lang::ParseOptions& options);

} // namespace SOMTParser::Lang::PddlInternal

#endif /* SOMTPARSER_LANGUAGES_PDDL_INTERNAL_HEADER */
