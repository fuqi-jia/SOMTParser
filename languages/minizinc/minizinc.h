/* -*- Header -*-
 *
 * MiniZinc frontend — the only header this language exposes.
 *
 * Everything else (lexer, parser, AST) stays inside languages/minizinc/src and
 * is neither installed nor added to the umbrella header, so twenty-two languages do
 * not inflate the public API surface.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_MINIZINC_HEADER
#define SOMTPARSER_LANGUAGES_MINIZINC_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

LanguagePtr mkMiniZincLanguage();

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_MINIZINC_HEADER */
