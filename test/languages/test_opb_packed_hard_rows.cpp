#include "somtparser/languages/opb.h"
#include "somtparser/hir/packed_linear_io.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <sstream>
#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

int main() {
    Lang::SourceUnit source;
    source.main_path = "large.opb";
    constexpr std::size_t rows = 65536;
    for (std::size_t i = 0; i < rows; ++i) {
        source.inline_source += "+0001 x01 -0000 x1 >= +0000 ;\n";
    }
    source.inline_source += "+9007199254740993 x01 -9007199254740992 x01 = 1 ;\n";
    source.inline_source += "+1 ~x1 >= 0 ;\n";  // complement remains ordinary HIR
    source.inline_source += "+1 x01 x1 < 1 ;\n"; // strict nonlinear row remains HIR
    source.inline_source += "+1 x1 != 2 ;\n";    // disequality remains HIR
    source.inline_source += "max: +17 x01 -3 x1 ;\n";
    auto parsed = Lang::mkOpbLanguage()->parse(source, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->packed_linear_rows);
    VERIFY(parsed.model->decls.size() == 2);
    VERIFY(parsed.model->decls[0].name == "x01");
    VERIFY(parsed.model->decls[1].name == "x1");
    for (const auto& declaration : parsed.model->decls) {
        VERIFY(declaration.sort.kind == H::SortKind::INT);
        VERIFY(declaration.lower_bound && declaration.upper_bound);
        VERIFY(declaration.lower_bound->name == "0");
        VERIFY(declaration.upper_bound->name == "1");
    }
    VERIFY(parsed.model->constraints.size() == 3);
    VERIFY(parsed.model->objectives.size() == 1);
    VERIFY(parsed.model->objectives[0].kind == H::ObjKind::MAXIMIZE);
    const auto& packed = *parsed.model->packed_linear_rows;
    std::size_t seen = 0;
    for (const auto& batch : packed.batches) {
        VERIFY(batch.source_file == "large.opb");
        for (const auto& row : batch.rows) {
            VERIFY(row.source_line == ++seen);
            VERIFY(row.end == row.begin + 2);
            if (seen <= rows) {
                VERIFY(packed.numbers[row.rhs] == "0");
                VERIFY(packed.numbers[batch.terms[row.begin].coefficient] == "1");
                VERIFY(packed.numbers[batch.terms[row.begin + 1].coefficient] == "0");
                VERIFY(batch.terms[row.begin].column == 0);
                VERIFY(batch.terms[row.begin + 1].column == 1);
            }
        }
    }
    VERIFY(seen == rows + 1);
    Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(*parsed.model, diagnostics));
    std::ostringstream target;
    VERIFY(H::writePackedLinearRowsSmt2(*parsed.model, {"x01", "x1"}, target, diagnostics));
    VERIFY(target.str().find("9007199254740993.0") != std::string::npos);
    VERIFY(target.str().find("9007199254740992.0") != std::string::npos);

    // Small files retain their existing public ordinary-HIR representation.
    source.inline_source = "+1 x01 +1 x1 >= 1 ;\n";
    parsed = Lang::mkOpbLanguage()->parse(source, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(!parsed.model->packed_linear_rows);
    VERIFY(parsed.model->constraints.size() == 1);
}
