/* -*- Header -*-
 *
 * QDIMACS 1.1 frontend — the only header this language exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_QDIMACS_HEADER
#define SOMTPARSER_LANGUAGES_QDIMACS_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkQdimacsLanguage();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_QDIMACS_HEADER */
