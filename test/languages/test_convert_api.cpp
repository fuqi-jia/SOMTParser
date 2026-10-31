#include "somtparser/translation/translate.h"
#include "test_helpers.h"
#include "somtparser/languages/register_all.h"

#include <sstream>
#include <stdexcept>
#include <streambuf>

using namespace SOMTParser;

namespace {
struct FailedWrite : std::streambuf {
    int_type overflow(int_type) override { return traits_type::eof(); }
};
struct FailedRead : std::streambuf {
    int_type underflow() override { throw std::runtime_error("read failed"); }
};
}

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    Lang::SourceUnit unit;
    unit.inline_source = "(declare-const x Int)(assert (>= x 2))(minimize x)(check-sat)";
    TranslateOptions opts;
    opts.language_id = "smtlib2";
    opts.dialect_name = "z3";
    const auto captured = translate(unit, opts);
    VERIFY(captured.exitCode() == 0);
    VERIFY(captured.diagnosticText().empty());
    VERIFY(captured.smt2().find("(minimize x)") != std::string::npos);
    VERIFY(captured.smt2().find("(check-sat)") != std::string::npos);

    std::istringstream input;
    std::ostringstream output, diagnostics;
    VERIFY(translate(unit, opts, &input, &output, &diagnostics).exitCode() == 0);
    VERIFY(output.str() == captured.smt2());
    VERIFY(diagnostics.str().empty());
    VERIFY(translate(unit, opts).smt2() == captured.smt2());

    FailedWrite failed_write;
    std::ostream bad_output(&failed_write);
    VERIFY(translate(unit, opts, &input, &bad_output, &diagnostics).exitCode() == 3);
    VERIFY(diagnostics.str() == "error: cannot write SMT-LIB output\n");

    opts.dialect_name = "invalid";
    const auto invalid = translate(unit, opts);
    VERIFY(invalid.exitCode() == 2);
    VERIFY(invalid.smt2().empty());
    VERIFY(invalid.diagnosticText() == "unknown dialect 'invalid'\n");

    opts.dialect_name = "z3";
    unit.inline_source.clear();
    unit.main_path = "-";
    std::istringstream model("(assert true)(check-sat)");
    std::ostringstream stdin_output, stdin_diagnostics;
    VERIFY(translate(unit, opts, &model, &stdin_output, &stdin_diagnostics).exitCode() == 0);
    VERIFY(stdin_diagnostics.str().empty());
    VERIFY(stdin_output.str().find("(check-sat)") != std::string::npos);

    std::istringstream empty;
    VERIFY(translate(unit, opts, &empty, &stdin_output, &stdin_diagnostics).exitCode() == 1);
    VERIFY(stdin_diagnostics.str() == "error: E_IO: stdin is empty\n");
    FailedRead failed_read;
    std::istream bad_input(&failed_read);
    std::ostringstream read_diagnostics;
    VERIFY(translate(unit, opts, &bad_input, &stdin_output, &read_diagnostics).exitCode() == 3);
    VERIFY(read_diagnostics.str() == "error: cannot read stdin\n");

    unit.main_path.clear();
    unit.inline_source = "aag 0 0 0 0 0\n";
    opts = {};
    opts.language_id = "aiger";
    opts.module = true;
    const auto module = translate(unit, opts);
    VERIFY(module.exitCode() == 0);
    VERIFY(module.smt2().find("; SOMT module interface ") == 0);
    VERIFY(module.smt2().find("(check-sat)") == std::string::npos);
    opts.profile_id = "default";
    opts.profile_explicit = true;
    const auto conflict = translate(unit, opts);
    VERIFY(conflict.exitCode() == 2);
    VERIFY(conflict.smt2().empty());
    VERIFY(conflict.diagnosticText() == "--module cannot be combined with --profile or --dialect\n");
}
