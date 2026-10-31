// Parser diagnostics belong on stderr, because stdout is the model.
//
// Every Parser::err_* used to write to std::cout. dumpSMT2()/toSmt2() hand back
// a script callers pipe straight into a solver, and somt-convert writes exactly
// that to its own stdout -- so a diagnostic on the same stream was spliced into
// the middle of the SMT-LIB text. It survived `2>/dev/null`, which is how a
// batch runner usually silences noise, and turned a visible failure into a
// corrupt model:
//
//     $ somt-convert bad.mzn 2>/dev/null
//     error: Kind mismatch of command "Type mismatch in add" in line 0.
//
// test/python/test_file_conversion_api.py checks conversion outcomes, including
// frontend rejection. This file also checks Parser::err_* directly, so that
// frontend-only fixtures cannot leave the underlying parser path untested.

#include "somtparser/frontend/parser.h"

#include <iostream>
#include <sstream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

/** Redirects a stream for its lifetime and hands back what was written. */
class Capture {
public:
    explicit Capture(std::ostream& s) : stream_(s), saved_(s.rdbuf(buffer_.rdbuf())) {}
    ~Capture() { stream_.rdbuf(saved_); }
    Capture(const Capture&) = delete;
    Capture& operator=(const Capture&) = delete;

    std::string text() const { return buffer_.str(); }

private:
    std::ostream&      stream_;
    std::stringstream  buffer_;
    std::streambuf*    saved_;
};

struct Streams {
    std::string out;
    std::string err;
    bool        parsed = false;
};

/** Parse @p script with both standard streams captured. */
Streams parseCapturing(const std::string& script) {
    Streams s;
    {
        Capture out(std::cout);
        Capture err(std::cerr);
        auto parser = std::make_shared<Parser>();
        s.parsed = parser->parseStr(script);
        s.out = out.text();
        s.err = err.text();
    }
    return s;
}

} // namespace

int main() {
    std::cout << "======= Parser diagnostics go to stderr =======\n";

    // A term whose argument sorts do not match: this is the exact path
    // (err_type_mis) whose message used to land in the translated output.
    {
        const Streams s = parseCapturing("(declare-fun b () Bool)\n(assert (+ b 1))\n");
        VERIFY(!s.parsed);
        VERIFY(!s.err.empty());
        VERIFY(s.err.find("error:") != std::string::npos);
        // The whole point: nothing at all on stdout.
        VERIFY(s.out.empty());
    }

    // An unknown symbol takes a different err_* function; the property is about
    // the family, not one member of it.
    {
        const Streams s = parseCapturing("(assert (no-such-operator 1 2))\n");
        VERIFY(!s.parsed);
        VERIFY(!s.err.empty());
        VERIFY(s.out.empty());
    }

    // A missing closing paren reaches err_unexp_eof.
    {
        const Streams s = parseCapturing("(assert (> 1 2)\n");
        VERIFY(!s.parsed);
        VERIFY(!s.err.empty());
        VERIFY(s.out.empty());
    }

    // A file that cannot be opened is a diagnostic too, and goes the same way.
    {
        Streams s;
        {
            Capture out(std::cout);
            Capture err(std::cerr);
            auto parser = std::make_shared<Parser>();
            s.parsed = parser->parse("test/instances/definitely-not-a-real-file.smt2");
            s.out = out.text();
            s.err = err.text();
        }
        VERIFY(!s.parsed);
        VERIFY(!s.err.empty());
        VERIFY(s.out.empty());
    }

    // The negative control. Without this, a Parser that had stopped reporting
    // anything at all would satisfy every check above.
    {
        const Streams s = parseCapturing("(declare-fun x () Int)\n(assert (> x 0))\n");
        VERIFY(s.parsed);
        VERIFY(s.err.empty());
        VERIFY(s.out.empty());
    }

    std::cout << "Parser diagnostics never touch stdout.\n";
    return 0;
}
