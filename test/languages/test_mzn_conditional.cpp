// MiniZinc `if c then a else b endif`.
//
// Two readings, and which one applies is decided by the TEST, not by the
// branches. That split is the whole content of this feature:
//
//   - a fixed test selects its branch at parse time and the others are never
//     elaborated;
//   - a test on a decision variable keeps both branches and becomes an ITE
//     term whose definedness obligation follows the selected branch only.
//
// The first reading is not an optimisation, and pinning it as one would miss
// what it is for. MiniZinc's own flattening folds a par conditional because a
// branch the test excludes may have no value at all -- `max(index_set(x))`
// guarded by `index_set(x) = {}` is the shape the upstream tenpenki model is
// written in. A frontend that elaborated both branches and then discarded one
// would have to give that branch a meaning first, and there is none to give.
// Worse, elaborating it has EFFECTS: a `let` declares variables into the
// model. So the untaken branch is skipped at the TOKEN level, and the test
// below that proves it names an identifier which does not exist.
//
// The second reading needs the relational adapter rather than a bare ITE:
// `Op::ITE` built directly would make both branches' definedness an
// obligation, which refuses models the specification accepts.

#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation mzn(const std::string& source) {
    Lang::SourceUnit unit;
    unit.inline_source = source;
    unit.display_name = "<conditional-test>";
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& fragment) {
    return text.find(fragment) != std::string::npos;
}

/** `=` is commutative and the builders canonicalize operand order, so the
 *  emitted equality may name either side first (CLAUDE.md invariant 2).
 *  Asserting the spelling that was written in would pin a shape the caller
 *  does not choose. */
bool hasEq(const std::string& text, const std::string& x, const std::string& y) {
    return has(text, "(= " + x + " " + y + ")")
        || has(text, "(= " + y + " " + x + ")");
}

std::string firstError(const Translation& translation) {
    for (const Diagnostic& diagnostic : translation.diagnostics().all()) {
        if (diagnostic.severity == Severity::ERROR) { return diagnostic.message; }
    }
    return "<no error>";
}

const char* kDecls =
    "int: k = 3;\n"
    "array[1..3] of var 0..9: a;\n";

} // namespace

int main() {
    std::cout << "======= MiniZinc: conditional expressions =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // A fixed test selects the `then`. The `else` must be ABSENT from the
        // output, not present-but-guarded: asserting only that the taken
        // branch appears would pass for an ITE that kept both.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 3 then a[1] = 1 else a[1] = 99 endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "1", "(select a 1)"));
        VERIFY(!has(smt, "99"));
        VERIFY(!has(smt, "ite"));
    }

    {
        // ...and a fixed FALSE test selects the `else`, symmetrically.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 4 then a[1] = 1 else a[1] = 99 endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "99", "(select a 1)"));
        VERIFY(!has(smt, "ite"));
    }

    {
        // THE property. The untaken branch names an identifier that was never
        // declared and indexes the array out of its declared range. Both would
        // be errors anywhere the parser actually looked. The model translates,
        // so the parser did not look -- which is what "skipped, not discarded"
        // means and is the only reading under which tenpenki's `max` over a
        // set the test just proved empty is well defined.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 3 then a[1] = 1\n"
              "           else a[99] = no_such_identifier endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(hasEq(translation.toSmt2(), "1", "(select a 1)"));
    }

    {
        // An `elseif` chain folds one test at a time. Here the FIRST test
        // fails and the second holds, so the middle arm is selected and both
        // the first and the last are gone.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 1 then a[2] = 11\n"
              "           elseif k = 3 then a[2] = 7\n"
              "           else a[2] = 55 endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "7", "(select a 2)"));
        VERIFY(!has(smt, "11"));
        VERIFY(!has(smt, "55"));
    }

    {
        // The same chain with the FIRST test holding. This is a separate case
        // because the token skip has to run PAST the chain's own `elseif` and
        // `else` keywords to the single `endif` that closes all of them.
        // Stopping at the first `else`, as skipping a lone branch does, leaves
        // those keywords in the stream and the item fails to parse -- which is
        // exactly how this was caught before it shipped.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 3 then a[2] = 7\n"
              "           elseif k = 1 then a[2] = 11\n"
              "           else a[2] = 55 endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "7", "(select a 2)"));
        VERIFY(!has(smt, "11"));
        VERIFY(!has(smt, "55"));
    }

    {
        // A test on a decision variable keeps both branches, as a term.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint a[3] = if a[1] > 0 then 5 else 6 endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "ite"));
        VERIFY(has(smt, "5"));
        VERIFY(has(smt, "6"));
    }

    {
        // Lazy definedness, and the reason `conditional` is called instead of
        // `mkOp(Op::ITE, …)`. `div` is partial, so the branch carries a
        // definedness obligation; the adapter emits it as
        // `ITE(test, defined(then), defined(else))`, which discharges it only
        // on the path that reaches the division. Building the ITE directly
        // DROPS that conjunct -- not over-asserts it, drops it -- and the
        // model then says nothing about the divisor at all.
        //
        // The test expression is deliberately `a[2] > 3` and not `a[1] != 0`.
        // With the latter the conditional's own test is TEXTUALLY THE SAME
        // expression as the definedness guard, so "the guard appears in the
        // output" is satisfied by the test's presence alone and the assertion
        // passes against the broken build. That is how the first version of
        // this case was written, and the breakage probe is what found it.
        const Translation translation = mzn(
            "array[1..2] of var 0..9: a;\n"
            "var int: q;\n"
            "constraint q = if a[2] > 3 then 100 div a[1] else 0 endif;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(ite (> (select a 2) 3) (div 100 (select a 1)) 0)"));
        // `distinct` is commutative and the builders canonicalize, so accept
        // either spelling of the guard -- but not its absence.
        VERIFY(has(smt, "(ite (> (select a 2) 3) (distinct 0 (select a 1)) true)")
               || has(smt, "(ite (> (select a 2) 3) (distinct (select a 1) 0) true)"));
    }

    {
        // `else` may be omitted when the `then` is Bool: the specification
        // supplies `true`, so a false test constrains nothing.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 9 then a[3] = 0 endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(!hasEq(translation.toSmt2(), "0", "(select a 3)"));
    }

    {
        // ...and with the test holding, the branch is asserted.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 3 then a[3] = 4 endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(hasEq(translation.toSmt2(), "4", "(select a 3)"));
    }

    {
        // An omitted `else` on a non-Bool conditional with a VAR test has no
        // value to supply. Refused as a type error naming the reason, rather
        // than defaulted to some zero that would silently answer a different
        // question.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint a[3] = if a[1] > 0 then 5 endif;\n"
              "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "without 'else'"));
    }

    {
        // MiniZinc joins Bool and Int through bool2int, including in a
        // conditional with a decision-variable test.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint a[1] = if a[2] > 0 then 5 else true endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(has(translation.toSmt2(), "(ite (> (select a 2) 0) 5 1)"));
    }

    {
        // Int and Set Int have no common conditional result sort.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint a[1] = if a[2] > 0 then 5 else {1} endif;\n"
              "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "both branches"));
    }

    {
        // Int and Real DO meet, by the same promotion an arithmetic operator
        // uses -- refusing this pair would be a gap the language does not have.
        const Translation translation = mzn(
            "array[1..1] of var 0..9: a;\n"
            "var float: r;\n"
            "constraint r = if a[1] > 0 then 1 else 2.5 endif;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(has(translation.toSmt2(), "ite"));
    }

    {
        // A non-Bool test is a type error, not a coercion.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k then a[1] = 1 else a[1] = 2 endif;\n"
              "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "test"));
    }

    {
        // A missing `endif` is malformed input -- E_PARSE, not a coverage gap.
        // The two codes feed different statistics and conflating them makes a
        // truncated file read as an unimplemented construct.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 3 then a[1] = 1 else a[1] = 2;\n"
              "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    {
        // Nesting: an inner `if` inside a skipped branch must not have its
        // `endif` mistaken for the outer one. If the depth count were wrong
        // the outer conditional would end early and the trailing tokens would
        // fail to parse.
        const Translation translation = mzn(
            std::string(kDecls)
            + "constraint if k = 4 then (if k = 1 then a[1] = 1 else a[1] = 2 endif)\n"
              "           else a[1] = 8 endif;\n"
              "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "8", "(select a 1)"));
        VERIFY(!has(smt, "ite"));
    }

    std::cout << "All MiniZinc conditional tests passed.\n";
    return 0;
}
