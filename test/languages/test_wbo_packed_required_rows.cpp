#include "somtparser/languages/opb.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

int main() {
    Lang::SourceUnit source;
    source.main_path = "required-weighted.wbo";
    const std::string top = "100000000000000000000000000000000000000000000000000000000000000000001";
    source.inline_source = "soft: " + top + " ;\n";
    constexpr std::size_t count = 65536;
    for (std::size_t i = 0; i < count; ++i) {
        source.inline_source += "[" + top + "] +1 x1 >= 1 ;\n";
    }
    source.inline_source += "[3] +1 x2 >= 1 ;\n";
    auto parsed = Lang::mkOpbLanguage()->parse(source, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->packed_linear_rows);
    VERIFY(parsed.model->decls.size() == 4); // x1,x2, one exact violation and one Int cost
    VERIFY(parsed.model->constraints.empty()); // all equalities/comparisons are packed
    VERIFY(!parsed.model->decls.back().lower_bound);
    VERIFY(!parsed.model->decls.back().upper_bound);
    VERIFY(parsed.model->objectives.size() == 1);
    VERIFY(parsed.model->objectives[0].kind == H::ObjKind::MINIMIZE);
    const auto& data = *parsed.model->packed_linear_rows;
    std::size_t seen = 0;
    for (const auto& batch : data.batches) {
        for (const auto& row : batch.rows) {
            if (++seen <= count) {
                VERIFY(row.source_line == seen + 1);
                VERIFY(row.relation == H::LinearRowRelation::GE);
                VERIFY(row.end == row.begin + 1);
                VERIFY(data.numbers[row.rhs] == "1");
                VERIFY(batch.terms[row.begin].column == 0);
                VERIFY(data.numbers[batch.terms[row.begin].coefficient] == "1");
            }
        }
    }
    VERIFY(seen == count + 4);
    Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(*parsed.model, diagnostics));
}
