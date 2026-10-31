// Multi-dimensional PARAMETER arrays.
//
// The decision-array side of this construct was flattened row-major long ago
// (flatIndex, recorded as an EncodingChoice). The parameter side was refused
// outright, with the message "this subset reads a flat list only" -- true of
// the reader and not of the format, which has written two-dimensional data as
// `[| row | row |]` all along. `multidimknapsack_simple.mzn` in the upstream
// corpus fails on nothing else.
//
// One asymmetry is worth stating because it is easy to get backwards. For a
// *decision* array the row-major flattening IS a choice: nothing in the
// emitted script distinguishes a flattened 2-D array from a 1-D one, so the
// decision is recorded. For a *parameter* array it is not a choice at all --
// `[| a, b | c, d |]` defines its own rows, the values are folded to literals
// at parse time, and no array reaches the output to be flattened. So there is
// no EncodingChoice here, and adding one would claim a decision the frontend
// did not make.
//
// What the frontend DOES have to do is check that the arrangement it was given
// is the arrangement that was declared. A 3x2 literal and an `array[1..2,1..3]`
// declaration agree on the cell count and disagree on everything else; reading
// the one against the other transposes the data and still translates. That is
// a wrong answer rather than a type error, which is the failure mode this
// frontend is organised against, and it is the case below that would catch it.

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
    unit.display_name = "<param-array-test>";
    TranslateOptions options;
    options.language_id = "minizinc";
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& fragment) {
    return text.find(fragment) != std::string::npos;
}

/** `=` is commutative and the builders canonicalize operand order, so an
 *  emitted equality may name either side first (CLAUDE.md invariant 2). */
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
    std::cout << "======= MiniZinc: multi-dimensional parameter arrays =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // Row-major, pinned CELL BY CELL. Asserting one corner would pass for
        // a column-major reading of a square array; all six is what makes the
        // convention checkable. The values fold to literals, so each
        // constraint below becomes an equality against a number.
        const Translation translation = mzn(
            "array[1..2,1..3] of int: W = [| 1, 2, 3\n"
            "                              | 4, 5, 6 |];\n"
            "array[1..6] of var 0..9: x;\n"
            "constraint x[1] = W[1,1];\n"
            "constraint x[2] = W[1,2];\n"
            "constraint x[3] = W[1,3];\n"
            "constraint x[4] = W[2,1];\n"
            "constraint x[5] = W[2,2];\n"
            "constraint x[6] = W[2,3];\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "(select x 1)", "1"));
        VERIFY(hasEq(smt, "(select x 2)", "2"));
        VERIFY(hasEq(smt, "(select x 3)", "3"));
        VERIFY(hasEq(smt, "(select x 4)", "4"));
        VERIFY(hasEq(smt, "(select x 5)", "5"));
        VERIFY(hasEq(smt, "(select x 6)", "6"));
    }

    {
        // THE transpose trap. Six cells either way, and only the declared
        // ARRANGEMENT distinguishes them. Refused by name; a frontend that
        // compared only the cell count would translate this and answer a
        // different question.
        const Translation translation = mzn(
            "array[1..2,1..3] of int: W = [| 1, 2\n"
            "                              | 3, 4\n"
            "                              | 5, 6 |];\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "3x2"));
        VERIFY(has(firstError(translation), "1..2,1..3"));
    }

    {
        // Index sets need not start at 1, and the offset is per dimension.
        const Translation translation = mzn(
            "array[0..1,0..1] of int: W = array2d(0..1,0..1, [7, 8, 9, 6]);\n"
            "array[1..2] of var 0..9: x;\n"
            "constraint x[1] = W[0,0];\n"
            "constraint x[2] = W[1,1];\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "(select x 1)", "7"));
        VERIFY(hasEq(smt, "(select x 2)", "6"));
    }

    {
        // Three dimensions, so the stride is not just "rows times columns".
        // Written as the format writes it: a 2-D literal cannot express three
        // dimensions, so this one is the shape check refusing to guess.
        const Translation translation = mzn(
            "array[1..2,1..2,1..2] of int: W = [| 1, 2 | 3, 4 |];\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    {
        // A ragged literal has no shape at all. Refused rather than padded:
        // padding invents cells the data never gave, and an SMT-LIB array
        // being total would read them as unconstrained rather than as missing.
        const Translation translation = mzn(
            "array[1..2,1..3] of int: W = [| 1, 2, 3\n"
            "                              | 4, 5 |];\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "ragged"));
    }

    {
        // A flat list has rank one; a rank-two declaration requires a
        // matching matrix or array2d constructor. MiniZinc rejects this
        // input as a type error, independent of constructor support.
        const Translation translation = mzn(
            "array[1..2,1..3] of int: W = [1, 2, 3, 4, 5, 6];\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode()
               == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "indexes differ"));
    }

    {
        // Wrong subscript ARITY is not an out-of-range index, and reporting it
        // as one sends the reader to look at the bounds.
        const Translation translation = mzn(
            "array[1..2,1..3] of int: W = [| 1, 2, 3 | 4, 5, 6 |];\n"
            "array[1..1] of var 0..9: x;\n"
            "constraint x[1] = W[1];\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "subscript"));
    }

    {
        // Out of range on the SECOND dimension only. A flattening that added
        // the offsets without checking each dimension would accept this and
        // read a cell from the next row -- in range for the flat vector and
        // wrong for the model.
        const Translation translation = mzn(
            "array[1..2,1..3] of int: W = [| 1, 2, 3 | 4, 5, 6 |];\n"
            "array[1..1] of var 0..9: x;\n"
            "constraint x[1] = W[1,4];\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "1..2,1..3"));
    }

    {
        // One-dimensional parameter arrays preserve non-default origins with
        // an explicit `array1d` constructor.
        const Translation translation = mzn(
            "array[0..2] of int: w = array1d(0..2, [5, 6, 7]);\n"
            "array[1..1] of var 0..9: x;\n"
            "constraint x[1] = w[0];\n"
            "solve satisfy;\n");
        VERIFY(translation.ok());
        VERIFY(hasEq(translation.toSmt2(), "(select x 1)", "5"));
    }

    {
        // The same value arriving as a top-level assignment rather than an
        // initializer -- the path a `.dzn` takes. The literal is read before
        // any declaration has been seen, so its rows and columns have to be
        // remembered until the declaration says what they are indexed from.
        const Translation translation = mzn(
            "int: n = 2;\n"
            "int: m = 3;\n"
            "array[1..n,1..m] of int: W;\n"
            "array[1..2] of var 0..9: x;\n"
            "constraint x[1] = W[1,3];\n"
            "constraint x[2] = W[2,1];\n"
            "solve satisfy;\n"
            "W = [| 1, 2, 3 | 4, 5, 6 |];\n");
        VERIFY(translation.ok());
        const std::string smt = translation.toSmt2();
        VERIFY(hasEq(smt, "(select x 1)", "3"));
        VERIFY(hasEq(smt, "(select x 2)", "4"));
    }

    {
        // ...and the shape check applies on that path too, or it would be a
        // check that lives on one of the two ways a value arrives.
        const Translation translation = mzn(
            "array[1..2,1..3] of int: W;\n"
            "solve satisfy;\n"
            "W = [| 1, 2 | 3, 4 | 5, 6 |];\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(translation), "3x2"));
    }

    {
        // A two-dimensional literal for a one-dimensional declaration.
        const Translation translation = mzn(
            "array[1..4] of int: w = [| 1, 2 | 3, 4 |];\n"
            "solve satisfy;\n");
        VERIFY(!translation.ok());
        VERIFY(translation.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    {
        // A parameter array whose ELEMENT TYPE is a named set. A set of
        // integers is an integer type with a domain, so the array is an int
        // array; what the set adds is a check that every value belongs to it.
        //
        // The `var` path has read this spelling since battleships. The
        // parameter path refused it, although the check is MORE necessary
        // here: a parameter is a constant, so an out-of-domain cell cannot be
        // ruled out later by a solver the way a decision variable's can. If
        // it is not caught at the declaration it is not caught at all.
        const Translation t = mzn(
            "set of int: colours = {1, 2, 5};\n"
            "array[1..3] of colours: c = [1, 5, 2];\n"
            "var 1..9: x;\n"
            "constraint x = c[2];\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "5"));       // c[2] inlined its value
    }
    {
        // ...and a cell outside the set is refused, naming the cell and the
        // set. Without this the array would translate with a value the source
        // says is impossible.
        const Translation t = mzn(
            "set of int: colours = {1, 2, 5};\n"
            "array[1..3] of colours: c = [1, 4, 2];\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(t.diagnostics().all()[0].message, "colours"));
    }
    {
        // The pre-pass binds a scalar DECLARATION that carries its own value,
        // not only a bare assignment item, because another item's value may
        // name it. `loc = [b, a];` cannot fold until `a` and `b` do, and they
        // are written `int: a = 1;`.
        //
        // The pre-pass sweeps to a fixed point, so the order within the file
        // does not matter -- which is the point: MiniZinc items may appear in
        // any order and a reader that depended on one would reject valid
        // models for where their lines sit.
        const Translation t = mzn(
            "array[1..2] of int: loc;\n"
            "loc = [b, a];\n"
            "int: a = 1;\n"
            "int: b = 2;\n"
            "var 1..9: x;\n"
            "constraint x = loc[1];\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(hasEq(t.toSmt2(), "x", "2"));   // loc[1] is b, which is 2
    }

    {
        // A set COMPREHENSION is refused as the construct it is, not as a
        // missing brace. Falling through to the literal's closing
        // `expectPunct("}")` gave "expected '}'" -- a message that points at
        // punctuation and files a feature this reader does not have under
        // "malformed input". The upstream corpus test rejects it on message
        // quality alone, which is how this was found.
        // In EXPRESSION position, which is where blocksworld writes it
        // (`on[s, b] in {c | c in blocks where c != b} union {-b}`). A
        // top-level `set of int: s = …` declaration is read by a different
        // parser, and putting the comprehension there tests nothing about
        // this guard -- the first version of this test did, and passed with
        // the guard deleted.
        // `c` is declared, as it is in blocksworld (`int: c = 3;`). Without
        // that the first element fails as an undeclared identifier and the
        // `|` is never reached -- so the test would be exercising name
        // resolution rather than this guard.
        // A set comprehension in EXPRESSION position now expands rather than
        // being refused. The generators are parse-time constants, so it
        // unrolls to its elements here exactly as `parseSetTerm` already did
        // where a `set of int:` VALUE is expected -- same machinery, a
        // different representation, because this position builds a term.
        //
        // The `where` is what makes this discriminate: `blocks` is 1..3 and
        // `b` is 2, so a reader that expanded the generator and dropped the
        // filter would produce {1,2,3} and still translate.
        const Translation t = mzn(
            "set of int: blocks = 1..3;\n"
            "int: b = 2;\n"
            "var 1..3: x;\n"
            "constraint x in {c | c in blocks where c != b};\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        // Shared finite-membership lowering preserves the filtered values;
        // this frontend need not force native set syntax on the SMT target.
        const std::string filtered = t.toSmt2();
        VERIFY(hasEq(filtered, "x", "1"));
        VERIFY(hasEq(filtered, "x", "3"));
        VERIFY(!hasEq(filtered, "x", "2"));
        // ...and an ordinary set literal is untouched by the check. Written
        // as a declaration rather than in expression position because a set
        // literal is what a named set's VALUE is, and that is the form this
        // subset reads; the guard sits on the shared literal parser either
        // way, so deleting it would still let the comprehension above
        // through.
        const Translation ok = mzn("set of int: s = {1, 2, 3};\n"
                                   "array[s] of int: p = [7, 8, 9];\n"
                                   "var 1..9: x;\nconstraint x = p[2];\n"
                                   "solve satisfy;\n");
        VERIFY(ok.ok());
    }
    {
        // `union` and `intersect` between set terms, in the operand position
        // of `in` -- which is how blocksworld writes it:
        // `on[s, b] in {c | c in blocks where c != b} union {-b}`.
        //
        // Read only in that position on purpose. The fixed-set path already
        // reads them where a `set of int:` value is expected, and those two
        // are the whole of where this subset needs them; putting them in the
        // general precedence chain would change how every arithmetic
        // expression parses to reach two constructs.
        const Translation t = mzn(
            "set of int: blocks = 1..3;\n"
            "int: b = 2;\n"
            "var -3..3: x;\n"
            "constraint x in {c | c in blocks where c != b} union {-b};\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const std::string united = t.toSmt2();
        VERIFY(hasEq(united, "x", "1"));
        VERIFY(hasEq(united, "x", "3"));
        VERIFY(hasEq(united, "x", "(- 2)"));
        VERIFY(!hasEq(united, "x", "2"));
    }

    {
        // A predicate parameter typed by a named set, declared `var`.
        //
        // The set NARROWS THE ARGUMENT, and the narrowing is unconditional --
        // a fact about the variable rather than part of the predicate's truth
        // value -- so it is emitted as a hard constraint and not conjoined
        // into the call, which would invert under `not p(x)`.
        //
        // This is D35, and it was settled by running MiniZinc 2.10.1 rather
        // than by reading the Handbook, which does not say. The model below is
        // the experiment: `locs = 1..3`, an argument declared `var 1..10`, and
        // then `x = 7`. MiniZinc does not reject the program -- it accepts it
        // and its flattener reports "model inconsistency detected", emitting
        // `constraint bool_eq(false,true)`. The same model with a `var int`
        // parameter, with the call removed, or with `x = 2`, flattens cleanly.
        //
        // So a translation emitting nothing for the parameter's domain admits
        // x = 7, which the source forbids: an over-approximation, and one no
        // corpus file could have exposed, because every file in the corpus
        // passes an argument already inside the set and the two readings agree
        // there.
        const Translation t = mzn(
            "set of int: locs = 1..3;\n"
            "var 1..10: x;\n"
            "predicate p(var locs: l) = l >= 0;\n"
            "constraint p(x);\n"
            "constraint x = 7;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        // The narrowing reaches the script. z3 answers `unsat` on this, which
        // is MiniZinc's own verdict.
        VERIFY(has(t.toSmt2(), "(and (>= x 1) (<= x 3))"));
    }
    {
        // The discriminating half: WITHOUT the call, nothing narrows x, and
        // the same script is satisfiable. Asserted because the constraint
        // above would also appear if the frontend emitted the named set for
        // every variable that merely shares a sort with one.
        const Translation t = mzn(
            "set of int: locs = 1..3;\n"
            "var 1..10: x;\n"
            "predicate p(var locs: l) = l >= 0;\n"
            "constraint x = 7;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(!has(t.toSmt2(), "(and (>= x 1) (<= x 3))"));
    }
    {
        // The shape the corpus actually contains: the argument is an element
        // of an array declared over that same named set, so the narrowing is
        // entailed and the emitted constraint is redundant rather than
        // restricting. It is emitted anyway -- deciding redundancy would mean
        // computing containment, and a frontend that emits a constraint only
        // when it can prove it necessary is a frontend that stops emitting it
        // the day the proof gets harder.
        const Translation t = mzn(
            "set of int: locs = -3..3;\n"
            "array[1..2] of var locs: on;\n"
            "predicate clear(var locs: l) = l < 0;\n"
            "constraint clear(on[1]);\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        // The body is inlined against the argument, so the emitted script
        // constrains `on[1]` and not some fresh unconstrained `l`.
        VERIFY(has(t.toSmt2(), "(< (select on 1) 0)"));
    }
    {
        // The FIXED form still checks membership at the call, which is the
        // behaviour that must not regress: there the argument is a constant,
        // so the check is possible and refusing an out-of-domain one is the
        // only chance to catch it.
        const Translation t = mzn(
            "set of int: rows = {1, 2};\n"
            "predicate p(rows: r) = r > 0;\n"
            "constraint p(5);\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    std::cout << "All MiniZinc parameter-array tests passed.\n";
    return 0;
}
