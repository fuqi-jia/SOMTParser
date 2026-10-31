// String operators applied to STRING CONSTANTS.
//
// `test/lowering/test_lift_operator_sweep.cpp` covers every string operator
// already, and covered all three of the ones below while they were broken. It
// exercises each operator over a declared VARIABLE -- `(str.to_int t)` with `t`
// a String -- which is the right shape for a lift-and-lower round trip and
// reaches none of `simp_oper`'s constant folding. Folding only fires on a
// constant, so the sweep and the folder are disjoint by construction, and a
// whole class of defect sits in the gap.
//
// Three of them did, and an upstream corpus is what found them:
//
//   * `str.to_int` and `str.to_code` RAISED AN ERROR for an argument the
//     standard gives a value. Both are total in SMT-LIB -- a string that is not
//     a run of digits maps to -1, a string that is not one character maps to -1
//     -- so `(str.to_int "abc")` is a well-formed term, and erroring turned a
//     legal script into a parse failure.
//
//   * All three read `toString()`, which renders a string constant WITH its
//     quotes. So the digit test saw `"7"` rather than `7`, and `"a"` was three
//     characters long. Every literal took the error branch, including
//     `(str.to_int "7")`. `getStringLiteral()` is the accessor for the value,
//     and `str.len` two cases above was already using it.
//
// The assertions here are on the VALUE, not on acceptance: each expression is
// folded and compared against what the standard says it equals, so a folder
// that returns the wrong number fails rather than a folder that merely returns.

#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

/** Parse `(assert <e>)` and report what it folded to. A fully folded true is
 *  the only outcome that means "the value is what the standard says". */
bool foldsTrue(const std::string& e) {
    ParserPtr p = newParser();
    if (!p->parseStr("(assert " + e + ")\n(check-sat)\n")) { return false; }
    const std::string out = p->dumpSMT2();
    return out.find("(assert true)") != std::string::npos;
}

} // namespace

int main() {
    std::cout << "======= string operators over constants =======\n";

    // ---- str.to_int: total, and -1 is a value rather than an error. ---------
    VERIFY(foldsTrue("(= (str.to_int \"7\") 7)"));
    // Leading zeroes are digits. "0007" is a run of digits, so it is 7 -- not
    // -1, which is what a reader that rejected the spelling would give.
    VERIFY(foldsTrue("(= (str.to_int \"0007\") 7)"));
    VERIFY(foldsTrue("(= (str.to_int \"abc\") (- 1))"));
    VERIFY(foldsTrue("(= (str.to_int \"\") (- 1))"));
    // A mixed string is not a run of digits, so it is -1 and not a prefix.
    VERIFY(foldsTrue("(= (str.to_int \"12a\") (- 1))"));
    VERIFY(foldsTrue("(= (str.to_int \"-3\") (- 1))"));

    // ---- str.to_code: the code point, or -1. -------------------------------
    VERIFY(foldsTrue("(= (str.to_code \"a\") 97)"));
    VERIFY(foldsTrue("(= (str.to_code \"A\") 65)"));
    VERIFY(foldsTrue("(= (str.to_code \"ab\") (- 1))"));
    VERIFY(foldsTrue("(= (str.to_code \"\") (- 1))"));

    // ---- str.is_digit: ONE digit character. --------------------------------
    //
    // Not `str.to_int`'s test with a different name: a run of digits is not a
    // digit. The two were sharing an implementation, which is how `"77"` came
    // back true.
    VERIFY(foldsTrue("(str.is_digit \"7\")"));
    VERIFY(foldsTrue("(not (str.is_digit \"77\"))"));
    VERIFY(foldsTrue("(not (str.is_digit \"a\"))"));
    VERIFY(foldsTrue("(not (str.is_digit \"\"))"));

    // ---- The neighbours, so the fix is not narrower than the class. --------
    VERIFY(foldsTrue("(= (str.len \"abc\") 3)"));
    VERIFY(foldsTrue("(= (str.++ \"ab\" \"c\") \"abc\")"));
    VERIFY(foldsTrue("(= (str.from_int 7) \"7\")"));
    // str.rev read the quoted rendering too, so it reversed the quotes along
    // with the characters and produced a string that was not the reverse of
    // anything.
    VERIFY(foldsTrue("(= (str.rev \"abc\") \"cba\")"));

    std::cout << "All string constant-folding tests passed." << std::endl;
    return 0;
}
