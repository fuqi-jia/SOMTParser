// `array2d(...)` and `_` in a decision array's initializer.
//
// `array2d(ROW, COL, [| … |])` states the index sets a literal is to be read
// under. This subset reads them to CHECK them rather than to reshape: the
// declaration already fixes the shape, so a wrapper that disagreed with it
// would be stating two different arrays. Checking is what makes accepting it
// safe -- ignoring the index sets would let a transposed model through in
// silence, which is the failure mode this tree is organised against.
//
// `_` means the cell is not fixed. MiniZinc leaves it to the solver, so it
// stays the decision variable it was declared as and NO equality is emitted
// for it. A parameter array may not have one: there is no solver to leave it
// to, which is why the hole is opt-in per call site rather than global.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/minizinc.h"
#include "somtparser/languages/register_all.h"

#include <cassert>
#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

Translation run(const std::string& src) {
    Lang::SourceUnit unit;
    unit.inline_source = src;
    unit.display_name = "t.mzn";
    TranslateOptions opts;
    opts.language_id = "minizinc";
    opts.profile_id = "ground";
    return translate(unit, opts);
}

/** How many cells this initializer FIXED.
 *
 *  Counted as `(assert (= ` rather than by looking for `(= (select a …`,
 *  because the builders canonicalize a commutative operator's argument order
 *  and the equality comes out `(= 1 (select a 0))` -- the constant first.
 *  CLAUDE.md invariant 2 is exactly this: never assert on the shape you
 *  passed in. The first version of this test did, and failed on output that
 *  was correct. */
std::size_t fixedCells(const std::string& smt);

bool has(const std::string& haystack, const std::string& needle) {
    return haystack.find(needle) != std::string::npos;
}

std::size_t count(const std::string& haystack, const std::string& needle) {
    std::size_t n = 0, at = 0;
    while ((at = haystack.find(needle, at)) != std::string::npos) { ++n; at += needle.size(); }
    return n;
}

std::size_t fixedCells(const std::string& smt) {
    std::size_t n = 0, at = 0;
    while ((at = smt.find("(assert (= ", at)) != std::string::npos) { ++n; at += 11; }
    return n;
}

} // namespace

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    std::cout << "======= MiniZinc: array2d and `_` =======\n";

    {
        // The index sets agree with the declaration, so the wrapper adds
        // nothing and the cells are fixed exactly as the flat list says.
        const Translation t = run(
            "array[1..2,1..2] of var 0..5: a = array2d(1..2, 1..2, [1,2,3,4]);\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(fixedCells(t.toSmt2()) == 4);
    }
    {
        // A disagreeing index set is refused rather than reshaped. Without
        // this check `array2d` would be a way to relabel an array's axes
        // silently.
        const Translation t = run(
            "array[1..2,1..2] of var 0..5: a = array2d(1..2, 1..3, [1,2,3,4]);\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == Uir::ErrorCode::E_TYPE);
    }
    {
        // ...and so is a wrapper that states the wrong NUMBER of dimensions.
        //
        // The first index set here MATCHES the declaration's first dimension,
        // deliberately. Written as `array1d(1..4, …)` the mismatch is caught
        // by the index-set check instead, and a breakage probe showed the
        // dimension-COUNT check could be deleted with the test still passing.
        // Making the one axis agree leaves only the count wrong, so only the
        // guard under test can refuse it.
        const Translation t = run(
            "array[1..2,1..2] of var 0..5: a = array1d(1..2, [1,2,3,4]);\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == Uir::ErrorCode::E_TYPE);
    }
    {
        // `_` fixes nothing. Three cells, one hole, so two equalities -- and
        // the declared domain still binds all three, because the hole is a
        // decision variable and not an absence.
        const Translation t = run(
            "array[1..3] of var 0..5: a = [1,_,3];\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(fixedCells(smt) == 2);
        VERIFY(count(smt, "(>= (select a ") == 3);   // the hole keeps its domain
    }
    {
        // Holes inside an `array2d`, which is the shape the upstream
        // battleships instances are written in.
        const Translation t = run(
            "array[1..2,1..2] of var 0..5: a = array2d(1..2, 1..2, [1,_,_,4]);\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(fixedCells(t.toSmt2()) == 2);
    }
    {
        // A PARAMETER array may not have a hole: there is no solver to leave
        // the cell to, so `_` there is an undeclared identifier and stays one.
        const Translation t = run("array[1..3] of int: p = [1,_,3];\n"
                                  "solve satisfy;\n");
        VERIFY(!t.ok());
    }
    {
        // An all-holes initializer is legal and fixes nothing, which is what
        // `branching on []`-style degenerate data looks like.
        const Translation t = run(
            "array[1..2] of var 0..5: a = [_,_];\nsolve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(fixedCells(t.toSmt2()) == 0);
    }

    // ---- the ASSIGNMENT-ITEM form: `a = array2d(…);` as its own item ------
    //
    // This is how the upstream battleships instances are written: the model
    // declares the array, the instance binds it. The value is carried as a
    // ParamArray, so a fixed cell inlines its constant at every use and a
    // hole resolves to the declared array's own element.
    {
        const Translation t = run(
            "array[1..2,1..2] of var 0..5: a;\n"
            "a = array2d(1..2, 1..2, [| 1, _ | _, 4 |]);\n"
            "constraint a[1,2] > 0;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // `a[1,2]` is the hole, so the CONSTRAINT reads it as the array and
        // not as a number.
        //
        // Asserted on the constraint, not on the presence of "select a"
        // anywhere: every cell's declared domain already emits two selects,
        // so that weaker form holds however the hole is read. A breakage
        // probe made the hole read as a constant and the test still passed.
        VERIFY(has(smt, "(assert (> (select a 1) 0))"));
    }
    {
        // A fixed cell still inlines, so a constraint that contradicts it
        // folds to false rather than reaching the solver as a variable.
        const Translation t = run(
            "array[1..2,1..2] of var 0..5: a;\n"
            "a = array2d(1..2, 1..2, [| 1, 2 | 3, 4 |]);\n"
            "constraint a[1,1] > 3;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "false"));
    }
    {
        // The declaration's shape must reach the value even when the index
        // sets cannot be folded until the instance supplies a parameter.
        // `array2d(ROW, COL, …)` has to evaluate ROW and COL, which a bare
        // `[| … |]` does not, so the pre-pass gives up on it and the main
        // pass is the first to bind the name at all. Reading the shape from
        // the DECLARATION rather than from a previous binding is what covers
        // both orders -- without it `a[1,2]` was refused as "indexed by 1
        // subscript but read with 2", and only files whose uses happened to
        // come earlier survived.
        const Translation t = run(
            "int: n;\n"
            "set of int: ROW = 1..(n+1);\n"
            "array[ROW,ROW] of var 0..5: a;\n"
            "n = 1;\n"
            "a = array2d(ROW, ROW, [| 1, _ | _, 4 |]);\n"
            "constraint a[1,2] > 0;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(assert (> (select a 1) 0))"));
    }
    {
        // A value whose cell count disagrees with the declaration is refused
        // rather than read against the wrong shape.
        const Translation t = run(
            "array[1..2,1..2] of var 0..5: a;\n"
            "a = array2d(1..2, 1..2, [1,2,3]);\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == Uir::ErrorCode::E_TYPE);
    }

    std::cout << "All MiniZinc array2d tests passed.\n";
    return 0;
}
