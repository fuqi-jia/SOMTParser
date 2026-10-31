/* -*- Header -*-
 *
 * Sygus frontend — the only header this language exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_SYGUS_HEADER
#define SOMTPARSER_LANGUAGES_SYGUS_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkSygusLanguage();

} // namespace SOMTParser::Lang

#endif
