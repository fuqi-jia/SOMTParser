/* -*- Header -*-
 *
 * TPTP frontend (CNF and FOF) — the only header this language exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_TPTP_HEADER
#define SOMTPARSER_LANGUAGES_TPTP_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkTptpLanguage();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_TPTP_HEADER */
