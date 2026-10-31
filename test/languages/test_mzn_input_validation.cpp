// The MiniZinc frontend, tested directly rather than through the CLI.
//
// Until now it had no test of its own: it was exercised only by the CLI
// contract script (one accepting and one rejecting fixture) and by the Python
// suite. Everything below is a case where it used to accept an input it should
// have refused, or crash on one it should have refused -- and none of them were
// reachable through those two fixtures.
//
// Refusing input is the point of this file. A frontend that quietly accepts a
// model it did not understand produces an SMT script for a different problem,
// and the experiment records it as a successful translation. That is worse than
// a recorded failure, so each case asserts the ErrorCode too: the code is the
// bucket the evaluation counts the failure in.

#include "somtparser/languages/minizinc.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/hir/typecheck.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Lang::ParseOutcome parseSource(const std::string& src) {
    auto lang = Lang::mkMiniZincLanguage();
    Lang::SourceUnit unit;
    unit.display_name = "<test>";
    unit.inline_source = src;
    Lang::ParseOptions opts;
    return lang->parse(unit, opts);
}

Lang::ParseOutcome parsePath(const std::string& path) {
    auto lang = Lang::mkMiniZincLanguage();
    Lang::SourceUnit unit;
    unit.main_path = path;
    unit.display_name = path;
    Lang::ParseOptions opts;
    return lang->parse(unit, opts);
}

bool rejects(const Lang::ParseOutcome& out, ErrorCode code) {
    if (out.ok()) { return false; }
    if (!out.diagnostics.hasErrors()) { return false; }
    return out.diagnostics.firstErrorCode() == code;
}

bool mentions(const Lang::ParseOutcome& out, const std::string& needle) {
    for (const auto& d : out.diagnostics.all()) {
        if (d.message.find(needle) != std::string::npos) { return true; }
    }
    return false;
}

/** Every error carries a line, so a benchmark author can find the item. */
bool located(const Lang::ParseOutcome& out) {
    for (const auto& d : out.diagnostics.all()) {
        if (d.severity == Severity::ERROR && d.loc.line > 0) { return true; }
    }
    return false;
}

std::string nested(int depth) {
    std::string s = "var int: x;\nconstraint ";
    s += std::string(static_cast<std::size_t>(depth), '(');
    s += "x";
    s += std::string(static_cast<std::size_t>(depth), ')');
    s += " > 0;\nsolve satisfy;\n";
    return s;
}

} // namespace

int main() {
    std::cout << "======= MiniZinc frontend =======\n";

    // ---- Accepted. Without these, refusing everything would pass the rest. --
    {
        const auto out = parseSource("var 1..5: x;\nconstraint x > 2;\nsolve minimize x;\n");
        VERIFY(out.ok());
        VERIFY(!out.diagnostics.hasErrors());
        VERIFY(out.model->decls.size() == 1);
        VERIFY(out.model->constraints.size() == 1);
        VERIFY(out.model->objectives.size() == 1);
        // The declared range became bounds rather than being dropped.
        VERIFY(out.model->decls[0].lower_bound && out.model->decls[0].upper_bound);
    }
    {
        const auto out = parseSource("var bool: b;\nconstraint b;\nsolve satisfy;\n");
        VERIFY(out.ok());
    }

    // ---- Exactly one solve item. --------------------------------------------
    // "A MiniZinc model must have exactly one solve item" (MiniZinc spec,
    // Items). Neither half was enforced, and both are silent wrong answers.
    {
        // With no solve item, every one of these translated to
        // `(set-logic ALL) (check-sat) (exit)` and exited 0 -- a benchmark that
        // was never read at all counted as a successful translation.
        VERIFY(rejects(parseSource("   \n\t \n"), ErrorCode::E_PARSE));
        VERIFY(rejects(parseSource("% just a comment\n"), ErrorCode::E_PARSE));
        VERIFY(rejects(parseSource("var int: x;\nconstraint x > 0;\n"), ErrorCode::E_PARSE));
        VERIFY(mentions(parseSource("% nothing\n"), "no solve item"));
        // ...including an actually empty file, which is the case a
        // whitespace-only inline_source cannot stand in for: SourceUnit says
        // inline_source "takes precedence when non-empty", so an empty one
        // falls back to opening main_path.
        VERIFY(rejects(parsePath("languages/minizinc/instances/reject/empty.mzn"),
                       ErrorCode::E_PARSE));
    }
    {
        // Two solve items silently became a two-objective OMT problem nobody
        // wrote.
        const auto out = parseSource(
            "var int: x;\nsolve minimize x;\nsolve maximize x;\n");
        VERIFY(rejects(out, ErrorCode::E_PARSE));
        VERIFY(mentions(out, "exactly one solve item"));
        VERIFY(located(out));
    }

    // ---- Bounded recursion. -------------------------------------------------
    // 5000 nested parens segfaulted the process, taking a batch run -- and any
    // embedding Python interpreter -- with it.
    {
        // Well inside the limit, so the limit is not merely "refuse everything".
        VERIFY(parseSource(nested(50)).ok());

        const auto out = parseSource(nested(5000));
        VERIFY(rejects(out, ErrorCode::E_PARSE));
        VERIFY(mentions(out, "nests more than"));
    }
    {
        // "not not not ..." recurses through parseAtom directly rather than
        // through the parenthesis rule, so it is a second cycle to bound.
        std::string s = "var bool: b;\nconstraint ";
        for (int i = 0; i < 5000; ++i) { s += "not "; }
        s += "b;\nsolve satisfy;\n";
        VERIFY(rejects(parseSource(s), ErrorCode::E_PARSE));
    }

    // ---- Integer literals that do not fit. ----------------------------------
    // std::stoll threw out_of_range, caught only by the frontend's blanket
    // handler, which filed a plain input error as E_INTERNAL -- the bucket
    // reserved for broken invariants -- with no source location at all.
    {
        const auto out = parseSource(
            "var int: x;\nconstraint x > 99999999999999999999999;\nsolve satisfy;\n");
        VERIFY(rejects(out, ErrorCode::E_PARSE));
        VERIFY(mentions(out, "64-bit"));
        VERIFY(located(out));
    }
    {
        // Also in a range bound, which reads integers through a different site.
        const auto out = parseSource(
            "var 1..99999999999999999999999: x;\nsolve satisfy;\n");
        VERIFY(rejects(out, ErrorCode::E_PARSE));
        VERIFY(located(out));
    }
    {
        // The largest value that does fit still parses.
        VERIFY(parseSource(
            "var int: x;\nconstraint x < 9223372036854775807;\nsolve satisfy;\n").ok());
    }

    // ---- A generated objective name must not collide. -----------------------
    // "obj" + index was minted without consulting the declarations, so
    // `var int: obj0; solve minimize obj0;` emitted
    // (define-objective obj0 OBJECTIVE_MIN obj0) -- rebinding the symbol the
    // script had just declared.
    {
        const auto out = parseSource(
            "var int: obj0;\nconstraint obj0 > 0;\nsolve minimize obj0;\n");
        VERIFY(out.ok());
        VERIFY(out.model->objectives.size() == 1);
        VERIFY(out.model->objectives[0].name != "obj0");
        for (const auto& d : out.model->decls) {
            VERIFY(d.name != out.model->objectives[0].name);
        }
    }
    {
        // The colliding name may be declared *after* the solve item: MiniZinc
        // items come in any order, so names are minted once the whole model is
        // parsed rather than at the moment the solve item is read.
        const auto out = parseSource(
            "var int: x;\nsolve minimize x;\nvar int: obj0;\n");
        VERIFY(out.ok());
        VERIFY(out.model->objectives.size() == 1);
        VERIFY(out.model->objectives[0].name != "obj0");
    }

    // ---- A directory is not a model. ----------------------------------------
    // On Linux an ifstream opens a directory successfully and reads it as the
    // empty string, so `somt-convert somedir.mzn` translated "nothing".
    {
        const auto out = parsePath("languages/minizinc/instances");
        VERIFY(rejects(out, ErrorCode::E_IO));
        VERIFY(mentions(out, "is a directory"));
    }
    {
        const auto out = parsePath("languages/minizinc/instances/no-such-file.mzn");
        VERIFY(rejects(out, ErrorCode::E_IO));
    }

    // ---- Locations point at the item, not at line 0. ------------------------
    {
        const auto out = parseSource("var int: x;\nvar int: y;\nconstraint @;\n");
        VERIFY(!out.ok());
        VERIFY(located(out));
        bool on_line_3 = false;
        for (const auto& d : out.diagnostics.all()) {
            if (d.loc.line == 3) { on_line_3 = true; }
        }
        VERIFY(on_line_3);
    }

    // ---- `div` and `mod` are implemented; `/` is a different question. ------
    //
    // This block used to assert that all three were refused by name, which was
    // right while the HIR had no integer division. It has three now, MiniZinc's
    // convention is truncation (Handbook), and the frontend names DIV_TRUNC --
    // test/languages/test_division_conventions.cpp holds it apart from
    // SMT-LIB's Euclidean div, which is the assertion that matters.
    {
        for (const char* op : {"div", "mod"}) {
            const std::string src =
                std::string("var 1..9: x;\nvar 1..9: y;\nconstraint y = x ") + op
                + " 2;\nsolve satisfy;\n";
            const auto out = parseSource(src);
            VERIFY(out.ok());
        }
    }
    {
        // `/` is REAL division whatever its operands are, so `x / 2` is a Real
        // term. Assigning it to a `var int` is a type error in MiniZinc and is
        // NOT one here: SMT-LIB makes Int a subtype of Real, so `(= y (/ x 2))`
        // is well-sorted and typeCheck accepts it.
        //
        // That is a leniency, recorded rather than asserted away. It admits a
        // model MiniZinc's own type checker rejects, which costs nothing on
        // valid input and means an invalid model translates instead of being
        // reported. Catching it needs MiniZinc's type rules rather than the
        // HIR's, which this subset does not implement.
        const auto out =
            parseSource("var 1..9: x;\nvar 1..9: y;\nconstraint y = x / 2;\nsolve satisfy;\n");
        VERIFY(out.ok());
        Uir::Diagnostics d;
        VERIFY(Uir::Hir::typeCheck(*out.model, d));
    }
    {
        // And the gap is in the machine-readable channel too. This used to read
        // 8/8 with an empty `missing` -- COMPLETE to anything calling
        // coverage() -- while `x div 2` was refused. A source comment saying
        // "the number is about the subset" does not reach that caller.
        Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
        Lang::Language* mzn = Lang::LanguageRegistry::instance().byId("minizinc");
        VERIFY(mzn != nullptr);
        VERIFY(mzn->coverage().supported < mzn->coverage().total);
        VERIFY(mzn->coverage().missing.size()
               == mzn->coverage().total - mzn->coverage().supported);
    }

    std::cout << "All MiniZinc frontend tests passed." << std::endl;
    return 0;
}
