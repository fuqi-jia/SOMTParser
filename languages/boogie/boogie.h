/* -*- Header -*-
 *
 * Boogie frontend (straight-line core) — the only header this language exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_BOOGIE_HEADER
#define SOMTPARSER_LANGUAGES_BOOGIE_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkBoogieLanguage();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_BOOGIE_HEADER */
