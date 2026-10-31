// `index_set(a)`, and `max`/`min`/`card` over a fixed set.
//
// These are parse-time values, and that is the design rather than a shortcut.
// A set in this subset has no HIR term to build -- `par_sets_` is read by
// declarations and never by the expression grammar -- so a set-valued
// expression does not denote a term, it denotes a value the parser knows.
// `max(index_set(x))` therefore folds to a number, which is precisely what
// makes `let { int: n = max(index_set(x)) } in ...` possible: `n` is used as
// an index bound by a declaration below it, and an index bound has to be a
// number before the array can be declared at all.
//
// The same reasoning makes `index_set(x) = {}` a truth value rather than a
// constraint, and that is what lets a conditional guarded by it FOLD (§4.7) --
// the shape `tenpenki.mzn.model` is written in, where the branch the guard
// excludes computes `max` of the set the guard just proved empty.
//
// Two bucket fixes ride along. `max` and `index_set` are names MiniZinc's own
// standard library defines; unimplemented, they fell through to the identifier
// path and were reported as `E_TYPE: undeclared identifier 'max'` -- a
// coverage gap filed as malformed input. Both now refuse by name where they
// are not implemented.

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
    unit.display_name = "<index-set-test>";
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& fragment) {
    return text.find(fragment) != std::string::npos;
}

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

} // namespace

int main() {
    std::cout << "======= MiniZinc: index_set and fixed-set folds =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // A decision array's index set, folded to its bounds.
        const Translation translation = mzn(
            "array[3..7] of var 0..9: a;\n"
            "array[1..3] of var 0..99: r;\n"
            "constraint r[1] = min(index_set(a));\n"
            "constraint r[2] = max(index_set(a));\n"
            "constraint r[3] = card(index_set(a));\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "(select r 1)", "3"));
        VERIFY(hasEq(smt, "(select r 2)", "7"));
        VERIFY(hasEq(smt, "(select r 3)", "5"));
    }

    {
        // A PARAMETER array has one too, and it is the declared index set
        // rather than 1..length -- an explicit `array1d` carries the declared
        // origin, and `index_set` must report what the model says.
        const Translation translation = mzn(
            "array[0..2] of int: w = array1d(0..2, [5, 6, 7]);\n"
            "array[1..2] of var 0..99: r;\n"
            "constraint r[1] = min(index_set(w));\n"
            "constraint r[2] = max(index_set(w));\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "(select r 1)", "0"));
        VERIFY(hasEq(smt, "(select r 2)", "2"));
    }

    {
        // THE guard shape. The comparison is a truth value, so the conditional
        // folds and the excluded branch -- which computes `max` of a set the
        // guard proved empty -- is never elaborated. Both polarities.
        const Translation nonempty = mzn(
            "array[1..3] of int: w = [1, 2, 3];\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint if index_set(w) = {} then r[1] = 0\n"
            "           else r[1] = max(index_set(w)) endif;\n"
            "solve satisfy;\n");
        VERIFY(nonempty.ok());
        VERIFY(hasEq(nonempty.toSmt2(), "(select r 1)", "3"));

        const Translation empty = mzn(
            "array[1..0] of int: w = [];\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint if index_set(w) = {} then r[1] = 0\n"
            "           else r[1] = max(index_set(w)) endif;\n"
            "solve satisfy;\n");
        VERIFY(empty.ok());
        VERIFY(hasEq(empty.toSmt2(), "(select r 1)", "0"));
    }

    {
        // `!=` is the same comparison the other way round.
        const Translation translation = mzn(
            "array[1..2] of int: w = [1, 2];\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint if index_set(w) != {} then r[1] = 9 else r[1] = 0 endif;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(hasEq(translation.toSmt2(), "(select r 1)", "9"));
    }

    {
        // A named parameter set on the right, and a range: the operand grammar
        // is the fixed-set one, not just `{}`.
        const Translation translation = mzn(
            "set of int: s = 1..3;\n"
            "array[1..3] of var 0..9: a;\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint if index_set(a) = s then r[1] = 1 else r[1] = 0 endif;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(hasEq(translation.toSmt2(), "(select r 1)", "1"));
    }

    {
        // `max` of an EMPTY set is undefined in MiniZinc. Refused rather than
        // given a sentinel: a sentinel is a number the source never wrote, and
        // the guarded conditional above is how a real model avoids reaching
        // this at all.
        const Translation translation = mzn(
            "array[1..0] of int: w = [];\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint r[1] = max(index_set(w));\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "empty set"));
    }

    {
        // ...but `card` of an empty set is 0, which is defined.
        const Translation translation = mzn(
            "array[1..0] of int: w = [];\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint r[1] = card(index_set(w));\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(hasEq(translation.toSmt2(), "(select r 1)", "0"));
    }

    {
        // `index_set` is defined for ONE-dimensional arrays; MiniZinc names
        // the dimension for the rest (`index_set_1of2`). Answering with the
        // flattened span would report this frontend's internal representation
        // as though the source had asked about it.
        const Translation translation = mzn(
            "array[1..2,1..3] of var 0..9: a;\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint r[1] = max(index_set(a));\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        VERIFY(has(firstError(translation), "one-dimensional"));
    }

    {
        // A non-array argument is a type error naming the reason.
        const Translation translation = mzn(
            "int: k = 3;\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint r[1] = max(index_set(k));\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(has(firstError(translation), "index set"));
    }

    {
        // The numeric overload is now implemented alongside fixed-set folds.
        // This must remain a scalar pair, not a failed range probe; the emitted
        // equality fixes r[1] to the larger operand.
        const Translation translation = mzn(
            "array[1..1] of var 0..99: r;\n"
            "constraint r[1] = max(3, 4);\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(hasEq(translation.toSmt2(), "(select r 1)", "4"));
    }

    {
        // A set literal comparison must NOT be hijacked by the fixed-set fold.
        // `{1, 2} = s` over a decision set is a constraint on `s`, and folding
        // it would answer a different question entirely. The probe fires only
        // on `index_set`, and this is the case that says so.
        //
        // The literal is on the LEFT deliberately. The probe looks at the
        // first token of the comparison, so `s = {1, 2}` never reaches it and
        // passes whether the probe is narrow or wide -- which is how the first
        // version of this case was written, and the breakage probe is what
        // found that it proved nothing.
        const Translation translation = mzn(
            "var set of int: s;\n"
            "constraint {1, 2} = s;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(has(smt, "(declare-fun s () (Set Int))"));
        VERIFY(has(smt, "set.insert"));
    }

    {
        // `card` over a DECISION set was already `Op::SET_CARD` and must stay
        // so. The fixed-set folds share their spellings with constructs over
        // decision values, so the ARGUMENT decides which a call is, not the
        // name -- dispatching on the name alone shadowed the existing `card`
        // and turned a supported construct into a refusal. `test_uir_sets`
        // caught that; this case is here so the test that describes the
        // feature covers its own collision.
        const Translation translation = mzn(
            "var set of 1..3: s;\n"
            "constraint card(s) > 1;\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(has(translation.toSmt2(), "set.card"));
    }

    {
        // ...and `max` over a decision set is NOT implemented, so it is
        // refused by name rather than silently read as a fixed-set fold.
        const Translation translation = mzn(
            "var set of 1..3: s;\n"
            "array[1..1] of var 0..99: r;\n"
            "constraint r[1] = max(s);\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }

    std::cout << "All MiniZinc index_set tests passed.\n";
    return 0;
}
