#pragma once
#include "somtparser/translation/translate.h"
namespace SOMTParser {
Translation translateImpl(const Lang::SourceUnit&, const TranslateOptions&,
                          Uir::Hir::ConstraintModelPtr,
                          const std::vector<Uir::Hir::LocatedExpr>&);
}
