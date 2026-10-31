/* -*- Header -*-
 *
 * FlatZinc frontend — the only header this language exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_FLATZINC_HEADER
#define SOMTPARSER_LANGUAGES_FLATZINC_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkFlatZincLanguage();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_FLATZINC_HEADER */
