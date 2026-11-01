#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <functional>
#include <algorithm>
#include <fstream>
#include <filesystem>
#include <cstdint>

using namespace SOMTParser;

static void verifyRange(const Command& command, const std::string& source) {
    VERIFY(command.range.end.offset >= command.range.begin.offset);
    for (const auto position : {command.range.begin, command.range.end}) {
        VERIFY(position.offset <= source.size());
        VERIFY(position.line == 1 + static_cast<size_t>(std::count(
            source.begin(), source.begin() + position.offset, '\n')));
        const auto newline = position.offset ? source.rfind('\n', position.offset - 1)
                                             : std::string::npos;
        VERIFY(position.column == position.offset -
            (newline == std::string::npos ? 0 : newline + 1) + 1);
    }
    VERIFY(source.substr(command.range.begin.offset,
                         command.range.end.offset - command.range.begin.offset) == command.original);
}

int main() {
    {
        Parser parser;
        parser.setCommandLogging(true);
        VERIFY(parser.getResultType() == RESULT_TYPE::RT_UNKNOWN);
        const std::string source =
            "(set-logic ALL)\n"
            "(assert (= (str.len \"Hello\") 5))\n"
            "(assert (= (str.len \"é\") 1))\n"
            "(assert (= (str.len \"\\u{e9}\") 1))\n"
            "(assert (= (str.replace_all \"abc\" \"\" \"x\") \"abc\"))\n"
            "(check-sat)\n";
        VERIFY(parser.parseStr(source, "regression.smt2"));
        VERIFY(parser.getSourceName() == "regression.smt2");
        VERIFY(parser.getSourceText() == source);
        VERIFY(parser.getScript().size() == 6);
        for (size_t i = 0; i < parser.getScript().size(); ++i) {
            const auto& command = parser.getScript()[i];
            VERIFY(command.index == i);
            VERIFY(command.range.end.offset >= command.range.begin.offset);
            VERIFY(source.substr(command.range.begin.offset,
                                 command.range.end.offset - command.range.begin.offset) ==
                   command.original);
        }
        VERIFY(parser.getScript()[1].expr != nullptr);
        VERIFY(std::string(parser.getScript()[1].kindName()) == "assert");
        VERIFY(parser.getScript()[5].isCheckSat());
        VERIFY(std::string(parser.getScript()[5].kindName()) == "check-sat");
        for (const auto& assertion : parser.getAssertions()) {
            VERIFY(assertion->isTrue());
        }
    }

    {
        // Reusing one parser must reset its source-position cursor for every
        // input entry point. Include CRLF, same-line commands, and byte columns.
        Parser parser;
        parser.setCommandLogging(true);
        const std::string first = "; é\r\n  (assert\n true) (check-sat)\n";
        VERIFY(parser.parseStr(first));
        for (const auto& command : parser.getScript().commands()) { verifyRange(command, first); }
        auto begin = parser.getScript().size();
        const std::string second = "\n\n(assert true)(check-sat)";
        VERIFY(parser.parseStr(second));
        for (size_t i = begin; i < parser.getScript().size(); ++i) { verifyRange(parser.getScript()[i], second); }
        const std::string third = " ; comment\n(assert true)\n(check-sat)";
        VERIFY(parser.loadStr(third));
        verifyRange(parser.nextCommand(), third);
        verifyRange(parser.nextCommand(), third);
        parser.nextCommand(); // consume EOF and release the incremental buffer

        const auto path = std::filesystem::temp_directory_path() /
            ("somt-position-" + std::to_string(reinterpret_cast<std::uintptr_t>(&parser)) + ".smt2");
        const std::string file_source = "(assert true)\n\n  (check-sat)";
        { std::ofstream file(path); file << file_source; }
        begin = parser.getScript().size();
        VERIFY(parser.parse(path.string()));
        std::filesystem::remove(path);
        for (size_t i = begin; i < parser.getScript().size(); ++i) { verifyRange(parser.getScript()[i], file_source); }
    }

    {
        // Many commands on one line exercise column tracking without assuming
        // line breaks between commands. No wall-clock assertion is needed.
        Parser parser;
        parser.setCommandLogging(true);
        std::string source;
        constexpr size_t count = 12000;
        for (size_t i = 0; i < count; ++i) { source += "(assert true)"; }
        VERIFY(parser.parseStr(source));
        VERIFY(parser.getScript().size() == count);
        verifyRange(parser.getScript()[0], source);
        verifyRange(parser.getScript()[count - 1], source);
        VERIFY(parser.getScript()[count - 1].range.end.column == source.size() + 1);
    }

    {
        Parser parser;
        parser.getOptions()->preserveOperators({
            NODE_KIND::NT_STR_REPLACE,
            NODE_KIND::NT_STR_REPLACE_ALL,
        });
        auto replacement = parser.mkExpr(
            "(str.replace_all \"a,b,a\" \"a\" \"\")");
        VERIFY(replacement != nullptr);
        VERIFY(replacement->isStrReplaceAll());
        VERIFY(replacement->getChildrenSize() == 3);

        VERIFY(parser.parseStr(
            "(set-logic QF_SLIA)\n"
            "(declare-const x String)\n"
            "(assert (= x (str.replace_all \"a,b,a\" \"a\" \"\")))\n"
            "(check-sat)\n"));
        bool found_replacement = false;
        std::function<void(const std::shared_ptr<DAGNode>&)> visit =
            [&](const std::shared_ptr<DAGNode>& node) {
                if (!node || found_replacement) return;
                if (node->isStrReplaceAll()) found_replacement = true;
                for (const auto& child : node->getChildren()) visit(child);
            };
        visit(parser.getAssertions().front());
        VERIFY(found_replacement);
    }

    {
        Parser parser;
        VERIFY(parser.parseStr(
            "(set-logic QF_UF)\n"
            "(declare-const p Bool)\n"
            "(check-sat-assuming (p))\n"));
        VERIFY(parser.getAssumptions().size() == 1);
        VERIFY(parser.getAssumptions().front().size() == 1);
        VERIFY(parser.getAssumptions().front().front()->toString() == "p");
    }

    {
        Parser parser;
        VERIFY(parser.parseStr("(assert false)\n(check-sat)\n"));
        VERIFY(parser.checkSat() == RESULT_TYPE::RT_UNSAT);
        VERIFY(parser.getResultType() == RESULT_TYPE::RT_UNSAT);
        VERIFY(parser.reset());
        VERIFY(parser.getResultType() == RESULT_TYPE::RT_UNKNOWN);
    }

    return 0;
}
