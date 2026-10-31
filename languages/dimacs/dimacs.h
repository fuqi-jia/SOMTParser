/* -*- Header -*-
 *
 * DIMACS CNF frontend — the only header this language exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_DIMACS_HEADER
#define SOMTPARSER_LANGUAGES_DIMACS_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkDimacsLanguage();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_DIMACS_HEADER */
