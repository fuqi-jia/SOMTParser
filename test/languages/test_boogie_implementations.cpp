#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"
#include "somtparser/frontend/parser.h"
#include "test_helpers.h"
#include <string>
#include <vector>

using namespace SOMTParser;

static Translation run(const std::string& source, bool horn) {
    Lang::SourceUnit unit;
    unit.main_path = "implementation.bpl";
    unit.inline_source = source;
    TranslateOptions options;
    options.language_id = "boogie";
    if (horn) { options.parse.options["chc"] = "1"; }
    return translate(unit, options);
}

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    const std::vector<std::string> accepted = {
        "implementation P(y:int,x:int) returns(w:int) { w:=y; } "
        "procedure P(x:int,y:int) returns(z:int); requires x<y; ensures z==x;",
        "procedure P(x:int) returns(r:int); ensures r==x; "
        "implementation P({:foo} y:int) returns({:bar} z:int) { z:=y; }",
        "procedure P(a,b:int) returns(c,d:int); ensures c==a && d==b; "
        "implementation P(x:int,y:int) returns(u,v:int) { u,v:=x,y; }",
        "procedure P(); implementation P() { var a:int; L: a:=1; assert a==1; } "
        "implementation P() { var a:bool; L: a:=true; assert a; }",
        "procedure P() { assert true; } implementation P() { assert false; }",
        "procedure P(x:int) returns(r:int); "
        "ensures (forall x:int :: x==x) && r==x; "
        "implementation P(y:int) returns(z:int) { z:=y; }"
    };
    const std::vector<std::pair<std::string, std::string>> rejected = {
        {"implementation P() { assert true; }", "no procedure declaration"},
        {"procedure P(x:int); implementation P() {}", "number of in-parameters"},
        {"procedure P() returns(x:int); implementation P() {}", "number of out-parameters"},
        {"procedure P(x:int); implementation P(x:bool) {}", "type for in-parameter"},
        {"procedure P() returns(x:int); implementation P() returns(y:bool) {}", "type for out-parameter"},
        {"procedure P(x,y:int); implementation P(a,a:int) {}", "declared more than once"},
        {"procedure P(x,x:int); implementation P(a,b:int) {}", "declared more than once"},
        {"procedure P(x:int) returns(y:int); implementation P(a:int) returns(a:int) {}", "declared more than once"},
        {"procedure P(x:int); implementation P(y:int) { y:=0; }", "immutable"},
        {"var g:int; procedure P(); implementation P() { g:=1; }", "modifies"},
        {"procedure P(); modifies missing; implementation P() {}", "mutable global"},
        {"var g:int; procedure P(g:int); implementation P(a:int) {}", "shadowing"},
        {"procedure P(); implementation P() ensures true; {}", "implementation body"},
        {"procedure P(x:int); implementation P(y:int where y>0) {}", "where"},
        {"procedure P(x:int); implementation P(y:int) { assert x==x; }", "not declared"},
        {"implementation P(z:int) {} procedure P(x:int); requires z>0;", "contract clause"},
        {"procedure P(x:int); requires old(x)>0; implementation P(y:int) {}", "old expressions"},
        {"procedure P() returns(x:int); requires x>0; implementation P() returns(y:int) {}", "precondition"},
        {"procedure P(); implementation P() { assert false;", "unterminated"}
    };
    for (bool horn : {false, true}) {
        for (const auto& source : accepted) {
            const auto translated = run(source, horn);
            if (!translated.ok()) {
                std::cerr << "rejected (horn=" << horn << "): " << source << '\n';
                for (const auto& diagnostic : translated.diagnostics().all()) {
                    std::cerr << diagnostic.message << '\n';
                }
            }
            VERIFY(translated.ok());
            ParserPtr parser = newParser();
            VERIFY(parser->parseStr(translated.toSmt2()));
        }
        for (const auto& [source, message] : rejected) {
            const auto translated = run(source, horn);
            if (translated.ok()) { std::cerr << "unexpected acceptance: " << source << '\n'; }
            VERIFY(!translated.ok());
            bool found = false;
            for (const auto& diagnostic : translated.diagnostics().all()) {
                found |= diagnostic.message.find(message) != std::string::npos;
            }
            if (!found) {
                std::cerr << "expected " << message << ": " << source << '\n';
                for (const auto& diagnostic : translated.diagnostics().all()) {
                    std::cerr << diagnostic.message << '\n';
                }
            }
            VERIFY(found);
        }
    }
}
