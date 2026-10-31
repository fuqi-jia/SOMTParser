/* -*- Header -*-
 * File/source conversion, including diagnostics, reports and output I/O.
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_CONVERT_HEADER
#define SOMTPARSER_TRANSLATION_CONVERT_HEADER

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <iosfwd>
#include <optional>
#include <string>

namespace SOMTParser {

/** Settings for convert(). Unset profile/dialect select "default"/"gomt".
 *  Module exports reject explicitly selected query profiles or dialects. */
struct ConvertOptions {
    std::string language;
    std::optional<std::string> profile;
    std::optional<std::string> dialect;
    Lang::ParseOptions parse;
    std::string report;
    bool module = false;
};

namespace detail {
inline TranslateOptions translateOptions(const ConvertOptions& options) {
    TranslateOptions result;
    result.language_id = options.language;
    result.profile_id = options.profile.value_or("default");
    result.profile_explicit = options.profile.has_value();
    result.dialect_name = options.dialect;
    result.dialect_explicit = options.dialect.has_value();
    result.parse = options.parse;
    result.report_path = options.report;
    result.module = options.module;
    return result;
}

} // namespace detail

[[deprecated("use translate(source, options)")]]
inline Translation convert(const Lang::SourceUnit& source, const ConvertOptions& options = {}) {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    return translate(source, detail::translateOptions(options));
}
[[deprecated("use translate(source, options, &input, &output, &diagnostics)")]]
inline Translation convert(const Lang::SourceUnit& source, const ConvertOptions& options,
                           std::istream& input, std::ostream& output, std::ostream& diagnostics) {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    return translate(source, detail::translateOptions(options), &input, &output, &diagnostics);
}

} // namespace SOMTParser
#endif
