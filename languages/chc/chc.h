/* -*- Header -*-
 *
 * CHC-COMP frontend (constrained Horn clauses) — the only header this language
 * exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_CHC_HEADER
#define SOMTPARSER_LANGUAGES_CHC_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkChcLanguage();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_CHC_HEADER */
