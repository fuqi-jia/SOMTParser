/* -*- Header -*-
 *
 * SMT-LIB 2 baseline frontend — the only header this language exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_SMTLIB2_HEADER
#define SOMTPARSER_LANGUAGES_SMTLIB2_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkSmtLib2Language();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_SMTLIB2_HEADER */
