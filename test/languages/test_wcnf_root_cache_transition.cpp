#include "somtparser/frontend/parser.h"
#include "somtparser/languages/wcnf.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <string>

static std::size_t count(const std::string& text, const std::string& token) {
    std::size_t result = 0, position = 0;
    while ((position = text.find(token, position)) != std::string::npos) {
        ++result;
        position += token.size();
    }
    return result;
}

int main() {
    using namespace SOMTParser;
    constexpr int width = 6000, small_roots = 12000;
    Lang::SourceUnit source;
    source.main_path = "cache-transition.wcnf";
    source.inline_source = "h";
    for (int i = 1; i <= width; ++i) {
        source.inline_source += " " + std::to_string(i);
    }
    source.inline_source += " 0\n";
    for (int i = 0; i < small_roots; ++i) {
        source.inline_source += i % 2 == 0 ? "7 -1 0\n" : "11 2 0\n";
    }
    auto language = Lang::mkWcnfLanguage();
    const auto parsed = language->parse(source, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->decls.size() == width);
    VERIFY(parsed.model->constraints.size() == small_roots + 1);
    VERIFY(!parsed.model->constraints.front().soft);
    for (int i = 0; i < small_roots; ++i) {
        const auto& row = parsed.model->constraints[i + 1];
        VERIFY(row.soft);
        VERIFY(row.weight_text == (i % 2 == 0 ? "7" : "11"));
        VERIFY(row.loc.line == i + 2);
    }
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    TranslateOptions options;
    options.language_id = "wcnf";
    options.omt_dialect = Lower::OmtDialect::Z3;
    const auto translated = translate(source, options);
    VERIFY(translated.ok() && !translated.usesPackedSmtStream());
    const auto text = translated.toSmt2();
    VERIFY(count(text, "(declare-fun ") == width);
    VERIFY(count(text, "(assert-soft ") == small_roots);
    VERIFY(count(text, ":weight 7") == small_roots / 2);
    VERIFY(count(text, ":weight 11") == small_roots / 2);
    VERIFY(translated.objectiveCount() == 1);
    auto reader = newParser();
    VERIFY(reader->parseStr(text));
    return 0;
}
