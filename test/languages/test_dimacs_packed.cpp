#include "somtparser/languages/dimacs.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

using namespace SOMTParser;

int main() {
    const auto language = Lang::mkDimacsLanguage();
    Lang::SourceUnit source;
    source.display_name = "packed.cnf";
    source.inline_source = "p cnf 4 3\n1\nc comment\n-2 0 0\n3 0\n";
    Lang::ParseOptions options;
    options.options["packed"] = "1";
    const auto result = language->parse(source, options);
    VERIFY(result.model);
    VERIFY(result.model->decls.empty());
    VERIFY(result.model->constraints.empty());
    VERIFY(result.model->bool_var_ranges.size() == 1);
    VERIFY(result.model->bool_var_ranges[0].count == 4);
    VERIFY(result.model->packed_bool_clauses.size() == 1);
    const auto& clauses = result.model->packed_bool_clauses[0];
    VERIFY(clauses.literals == (std::vector<std::int64_t>{1, -2, 3}));
    VERIFY(clauses.source_lines == (std::vector<std::uint32_t>{2, 4, 5}));
    VERIFY(clauses.clause_offsets == (std::vector<std::uint64_t>{0, 2, 2, 3}));
    VERIFY(clauses.weight_offsets == (std::vector<std::uint64_t>{0, 0, 0, 0}));

    source.inline_source = "p cnf 1 1\n1 0\n2 0\n";
    options.strict = true;
    VERIFY(!language->parse(source, options).model);
    options.strict = false;
    const auto expanded = language->parse(source, options);
    VERIFY(expanded.model);
    VERIFY(expanded.model->bool_var_ranges[0].count == 2);
    VERIFY(expanded.model->packed_bool_clauses[0].source_lines.size() == 2);
}
