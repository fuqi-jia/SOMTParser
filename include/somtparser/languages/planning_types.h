/* Internal finite type DAG shared by classical and hierarchical planning. */
#ifndef SOMTPARSER_LANGUAGES_PLANNING_TYPES_HEADER
#define SOMTPARSER_LANGUAGES_PLANNING_TYPES_HEADER

#include "somtparser/translation/diagnostic.h"

#include <functional>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace SOMTParser::Lang::PlanningInternal {

using TypeHierarchy = std::map<std::string, std::set<std::string>>;

inline bool validateTypes(const TypeHierarchy& types, const std::string& language,
                          Uir::Diagnostics& diagnostics) {
    for (const auto& [type, parents] : types) {
        for (const auto& parent : parents) {
            if (!types.count(parent)) {
                diagnostics.error(Uir::ErrorCode::E_TYPE,
                                  "type '" + type + "' has unknown parent '" + parent + "'");
                return false;
            }
        }
    }
    // A shared ancestor in a diamond is not a cycle: only a grey ancestor is.
    std::map<std::string, unsigned> colours;
    std::function<bool(const std::string&)> visit = [&](const std::string& type) {
        if (colours[type] == 2) { return true; }
        if (colours[type] == 1) {
            diagnostics.error(Uir::ErrorCode::E_TYPE,
                              "cyclic " + language + " type hierarchy at '" + type + "'");
            return false;
        }
        colours[type] = 1;
        for (const auto& parent : types.at(type)) {
            if (!visit(parent)) { return false; }
        }
        colours[type] = 2;
        return true;
    };
    for (const auto& [type, parents] : types) {
        if (!visit(type)) { return false; }
    }
    return true;
}

inline bool isSubtype(const TypeHierarchy& types, const std::string& actual,
                      const std::string& expected) {
    if (expected == "object") { return true; }
    std::vector<std::string> pending{actual};
    std::set<std::string> seen;
    while (!pending.empty()) {
        std::string type = std::move(pending.back());
        pending.pop_back();
        if (type == expected) { return true; }
        if (!seen.insert(type).second) { continue; }
        const auto found = types.find(type);
        if (found != types.end()) {
            pending.insert(pending.end(), found->second.begin(), found->second.end());
        }
    }
    return false;
}

} // namespace SOMTParser::Lang::PlanningInternal
#endif
