#include "somtparser/frontend/parser.h"
#include "test_helpers.h"
#include <chrono>
#include <filesystem>
#include <fstream>
#include <string>

using namespace SOMTParser;

static void checkPosition(const std::string& source, const SourcePosition& actual) {
    VERIFY(actual.offset <= source.size());
    size_t line = 1, column = 1;
    for (size_t i = 0; i < actual.offset; ++i) {
        if (source[i] == '\n') { ++line; column = 1; }
        else ++column;
    }
    VERIFY(actual.line == line);
    VERIFY(actual.column == column);
}

static void checkCommand(const std::string& source, const Command& command) {
    checkPosition(source, command.range.begin);
    checkPosition(source, command.range.end);
    VERIFY(command.range.end.offset >= command.range.begin.offset);
    VERIFY(source.substr(command.range.begin.offset,
        command.range.end.offset - command.range.begin.offset) == command.original);
    VERIFY(!command.original.empty() && command.original.front() == '(' && command.original.back() == ')');
}

int main() {
    const std::string first = "; header\r\n  (set-logic QF_LIA)\r\n\t(echo \"\xcf\x80\")\n"
        " (declare-const x Int) ; comment\n(assert\n (> x 0))\n(check-sat)\n";
    Parser parser;
    parser.setCommandLogging(true);
    VERIFY(parser.parseStr(first, "first.smt2"));
    VERIFY(parser.getScript().size() == 5);
    for (const auto& command : parser.getScript().commands()) checkCommand(first, command);
    const auto saved = parser.getScript()[0].range;
    VERIFY(saved.begin.offset == 12);
    VERIFY(saved.begin.line == 2 && saved.begin.column == 3);

    const size_t oldCount = parser.getScript().size();
    const std::string second = "\n\n(assert (< x 3))\n(check-sat)";
    VERIFY(parser.parseStr(second, "second.smt2"));
    VERIFY(parser.getSourceName() == "second.smt2");
    for (size_t i = oldCount; i < parser.getScript().size(); ++i)
        checkCommand(second, parser.getScript()[i]);
    VERIFY(parser.getScript()[0].range.begin.offset == saved.begin.offset);
    VERIFY(parser.getScript()[0].range.begin.line == saved.begin.line);
    VERIFY(parser.parseStr(""));
    VERIFY(parser.getSourceText() == second);

    Parser stream;
    stream.setCommandLogging(true);
    VERIFY(stream.loadStr(first, "stream.smt2"));
    size_t commands = 0;
    for (;;) {
        const auto command = stream.nextCommand();
        if (command.type == CMD_TYPE::CT_EOF) break;
        checkCommand(first, command);
        ++commands;
    }
    VERIFY(commands == 5);
    VERIFY(stream.loadStr(second, "replacement.smt2"));
    for (;;) {
        const auto command = stream.nextCommand();
        if (command.type == CMD_TYPE::CT_EOF) break;
        checkCommand(second, command);
    }

    const auto path = std::filesystem::temp_directory_path() / ("somt-source-positions-" +
        std::to_string(std::chrono::steady_clock::now().time_since_epoch().count()) + ".smt2");
    { std::ofstream out(path, std::ios::binary); out << first; VERIFY(out.good()); }
    Parser file;
    file.setCommandLogging(true);
    VERIFY(file.parse(path.string()));
    for (const auto& command : file.getScript().commands()) checkCommand(first, command);
    VERIFY(std::filesystem::remove(path));

    // Many logged assertions exercise the real command path. Checking each
    // expected range takes constant work; the test itself never rescans prefixes.
    const std::string assertion = "(assert true)\n";
    constexpr size_t count = 40000;
    std::string large;
    large.reserve(assertion.size() * count);
    for (size_t i = 0; i < count; ++i) large += assertion;
    Parser bulk;
    bulk.setCommandLogging(true);
    VERIFY(bulk.parseStr(large));
    VERIFY(bulk.getScript().size() == count);
    for (size_t i = 0; i < count; ++i) {
        const auto& range = bulk.getScript()[i].range;
        VERIFY(range.begin.offset == i * assertion.size());
        VERIFY(range.end.offset == (i + 1) * assertion.size() - 1);
        VERIFY(range.begin.line == i + 1 && range.end.line == i + 1);
        VERIFY(range.begin.column == 1 && range.end.column == assertion.size());
    }
}
