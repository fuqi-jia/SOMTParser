#include "somtparser/languages/xcsp3.h"
#include "somtparser/translation/translate.h"
#include "somtparser/frontend/parser.h"
#include "../test_helpers.h"

#include <string>
#include <vector>

using namespace SOMTParser;

int main() {
    Lang::LanguageRegistry::instance().add(Lang::mkXcsp3Language());
    TranslateOptions options;
    options.language_id = "xcsp3";
    options.omt_dialect = Lower::OmtDialect::Z3;

    struct Case { std::string declarations, constraints; bool accepted; unsigned variables; };
    const std::string sparse = "<array id=\"x\" size=\"[3]\">"
        "<domain for=\"x[0] x[2]\">0..1</domain></array>";
    const std::vector<Case> cases = {
        {sparse, "<intension>ne(x[0],x[2])</intension>", true, 2},
        {sparse, "", true, 2},
        {sparse + "<var id=\"y\" as=\"x\"/>",
            "<intension>ne(x[0],y[0])</intension>", true, 4},
        {"<var id=\"x\"/>", "", true, 1},
        {"<array id=\"x\" size=\"[2]\"/>", "", true, 2},
        {"<array id=\"x\" size=\"[2]\"><domain for=\"x[0]\"/></array>", "", true, 1},
        {sparse, "<intension>eq(x[1],0)</intension>", false, 0},
        {sparse, "<sum><list>x[]</list><condition>(eq,1)</condition></sum>", false, 0},
        {sparse + "<var id=\"y\" as=\"x[1]\"/>", "", false, 0},
        {"<var id=\"x\"/>", "<intension>eq(missing,0)</intension>", false, 0},
        {"<var id=\"x\">2..1</var>", "", false, 0}
    };
    for (const auto& item : cases) {
        Lang::SourceUnit source;
        source.main_path = "domain-case.xml";
        source.inline_source = "<instance format=\"XCSP3\" type=\"CSP\"><variables>"
            + item.declarations + "</variables><constraints>" + item.constraints
            + "</constraints></instance>";
        const auto result = translate(source, options);
        if (result.ok() != item.accepted) { std::cerr << result.report().toJson() << '\n'; }
        VERIFY(result.ok() == item.accepted);
        if (!item.accepted) { continue; }
        VERIFY(result.report().stats().num_vars == item.variables);
        const auto text = result.toSmt2();
        VERIFY(newParser()->parseStr(text));
        if (item.declarations == sparse || item.declarations.find("as=\"x\"") != std::string::npos) {
            VERIFY(text.find("x[1]") == std::string::npos);
            VERIFY(text.find("y[1]") == std::string::npos);
        }
    }
    for (const auto& path : {
             "languages/xcsp3/instances/ok/undefined_array_cells.xml",
             "languages/xcsp3/instances/ok/empty_domain.xml"}) {
        Lang::SourceUnit source;
        source.main_path = path;
        VERIFY(translate(source, options).ok());
    }
    Lang::SourceUnit refused;
    refused.main_path = "languages/xcsp3/instances/reject/undefined_array_operand.xml";
    VERIFY(!translate(refused, options).ok());
    return 0;
}
