#include "somtparser/languages/mps.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

int main() {
    Lang::SourceUnit source;
    source.main_path = "shared-defaults.mps";
    source.inline_source = "NAME defaults\nROWS\n N cost\nCOLUMNS\n";
    constexpr std::size_t count = 4096;
    for (std::size_t i = 0; i < count; ++i) {
        source.inline_source += " r" + std::to_string(i) + " cost 0\n";
    }
    source.inline_source += " mark0 'MARKER' 'INTORG'\n a cost 0\n b cost 0\n c cost 0\n"
        " mark1 'MARKER' 'INTEND'\n f cost 0\n n cost 0\n s cost 0\n q cost 0\n"
        "BOUNDS\n LO bounds c 2\n FR bounds f\n MI bounds n\n SC bounds s 3\n"
        " BV bounds q\nENDATA\n";
    auto parsed = Lang::mkMpsLanguage()->parse(source, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->decls.size() == count + 7);
    const auto& decls = parsed.model->decls;
    const auto zero = decls.front().lower_bound;
    VERIFY(zero && zero->kind == H::ExprKind::LIT_INT && zero->int_value == 0);
    for (std::size_t i = 0; i < count; ++i) {
        VERIFY(decls[i].lower_bound == zero);
        VERIFY(!decls[i].upper_bound);
        VERIFY(decls[i].sort.kind == H::SortKind::REAL);
        VERIFY(decls[i].loc.file == source.main_path);
        VERIFY(decls[i].loc.line == static_cast<int>(i + 5));
    }
    const auto& a = decls[count];
    const auto& b = decls[count + 1];
    const auto& c = decls[count + 2];
    VERIFY(a.lower_bound == zero && b.lower_bound == zero);
    VERIFY(a.upper_bound && a.upper_bound == b.upper_bound);
    VERIFY(a.upper_bound->kind == H::ExprKind::LIT_INT && a.upper_bound->int_value == 1);
    VERIFY(a.sort.kind == H::SortKind::INT && b.sort.kind == H::SortKind::INT);
    VERIFY(a.loc.line != b.loc.line);
    // An explicit lower-bound record disables the marker's default upper 1.
    VERIFY(c.lower_bound && c.lower_bound != zero && !c.upper_bound);
    VERIFY(c.sort.kind == H::SortKind::INT);
    for (const std::size_t index : {count + 3, count + 4, count + 5}) {
        VERIFY(!decls[index].lower_bound && !decls[index].upper_bound);
    }
    VERIFY(decls[count + 6].lower_bound && decls[count + 6].upper_bound);
    VERIFY(decls[count + 6].sort.kind == H::SortKind::INT);
    VERIFY(parsed.model->constraints.size() == 1); // semicontinuous zero-or-band
    H::ConstraintModel snapshot = *parsed.model;
    Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(snapshot, diagnostics));
    // Caches are scoped to this parse, so source locations never leak across files.
    source.main_path = "second-defaults.mps";
    const auto second = Lang::mkMpsLanguage()->parse(source, Lang::ParseOptions{});
    VERIFY(second.ok());
    VERIFY(second.model->decls.front().lower_bound != zero);
    VERIFY(second.model->decls.front().loc.file == source.main_path);
}
