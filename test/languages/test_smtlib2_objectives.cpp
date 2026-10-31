#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "test_helpers.h"
using namespace SOMTParser;
using namespace SOMTParser::Uir;

Translation run(const std::string& body) {
    Lang::SourceUnit unit;
    unit.inline_source = "(set-logic ALL)(declare-fun x () Int)" + body;
    TranslateOptions options;
    options.language_id = "smtlib2";
    options.omt_dialect = Lower::OmtDialect::Z3;
    return translate(unit, options);
}

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    const auto minimum = run("(assert (>= x 3))(minimize x)");
    VERIFY(minimum.ok());
    VERIFY(minimum.toSmt2().find("(minimize x)") != std::string::npos);
    const auto maximum = run("(maximize x)");
    VERIFY(maximum.ok());
    VERIFY(maximum.toSmt2().find("(maximize x)") != std::string::npos);
    const auto lex = run("(set-option :opt.priority lex)(minimize x)(maximize (- x))");
    VERIFY(lex.ok());
    VERIFY(lex.toSmt2().find("(maximize (- x))") != std::string::npos);
    VERIFY(!run("(minimize x)(maximize x)").ok());
    VERIFY(!run("(set-option :opt.priority box)(minimize x)").ok());
    VERIFY(!run("(minimize x :comp >)").ok());
    VERIFY(!run("(minimize x :epsilon 1)").ok());
    VERIFY(run("(assert-soft (> x 0))").ok());
    VERIFY(run("(minimize 0)").ok());
    VERIFY(!run("(assert-soft (> x 0))(minimize x)").ok());
    VERIFY(!run("(assert-soft (> x 0) :id a)(assert-soft (< x 0) :id b)").ok());
    return 0;
}
