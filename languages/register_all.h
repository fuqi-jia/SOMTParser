/* -*- Header -*-
 *
 * Explicit language registration.
 *
 * Not static initialisers: a static library only pulls in object files that
 * resolve a referenced symbol, so a translation unit containing nothing but a
 * registrar object is dropped by the linker. The behaviour differs across
 * MSVC, AppleClang and GCC, and --whole-archive is not portable. An explicit
 * call is the only reliable option.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LANGUAGES_REGISTER_ALL_HEADER
#define SOMTPARSER_LANGUAGES_REGISTER_ALL_HEADER

#include "somtparser/translation/language.h"

namespace SOMTParser::Lang {

/** Register every language built into somtparser_languages. Idempotent. */
void registerAllLanguages(LanguageRegistry& registry);

} // namespace SOMTParser::Lang

#endif /* SOMTPARSER_LANGUAGES_REGISTER_ALL_HEADER */
