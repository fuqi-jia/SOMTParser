/* -*- Header -*-
 *
 * LP (CPLEX/Gurobi) frontend — the only header this language exposes.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_LP_HEADER
#define SOMTPARSER_LANGUAGES_LP_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkLpLanguage();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_LP_HEADER */
