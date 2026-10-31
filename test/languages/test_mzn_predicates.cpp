// MiniZinc predicate items.
//
// A predicate is a *definition*, and that word decides the representation. The
// HIR's FunDecl is an uninterpreted function; declaring a predicate that way
// would throw its body away and let it denote anything, so constraints the model
// says are unsatisfiable would come back satisfiable. That is unsound in the
// permissive direction -- the same shape as docs/languages/hddl.md §4.1, one
// layer down -- and it is the failure this file is mostly about, because it does
// not look like a failure: the script is well-formed and the solver answers.
//
// The chosen route is inlining, which is exact and is what MiniZinc's own
// flattening does. Inlining has one hard edge: a recursive predicate does not
// terminate, so it must be refused rather than attempted.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/minizinc.h"
#include "somtparser/languages/register_all.h"
#include "test_helpers.h"
#include "somtparser/frontend/parser.h"
#include "translation/bound_semantics.h"

#include <cassert>
#include <iostream>
#include <string>
#include <vector>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.mzn";
    u.display_name = "t.mzn";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "minizinc";
    return translate(u, opts);
}

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

bool rejects(const std::string& src, ErrorCode code) {
    const Translation t = run(src);
    return !t.ok() && t.diagnostics().firstErrorCode() == code;
}

/** Just the `(assert …)` lines of a script.
 *
 *  Searching the whole script for a variable name proves nothing: every declared
 *  variable appears in its own declare-fun, so `smt.find("y")` succeeds even
 *  when no constraint mentions y. A probe that mutated the shared predicate body
 *  in place -- so that the second call re-emitted the first call's constraint --
 *  passed the whole file on exactly that hole. */
std::vector<std::string> assertions(const std::string& smt) {
    std::vector<std::string> out;
    std::size_t at = 0;
    while ((at = smt.find("(assert", at)) != std::string::npos) {
        const std::size_t end = smt.find('\n', at);
        out.push_back(smt.substr(at, end - at));
        at = end == std::string::npos ? smt.size() : end;
    }
    return out;
}

bool finiteDomainEquation(const std::string& smt, const std::string& cell,
                          const std::string& carrier) {
    for (const auto& assertion : assertions(smt)) {
        const auto first = assertion.find(cell);
        if (has(assertion, "(assert (= ") && has(assertion, "set.inter")
            && has(assertion, carrier) && first != std::string::npos
            && assertion.find(cell, first + cell.size()) != std::string::npos) {
            return true;
        }
    }
    return false;
}

} // namespace

int main() {
    std::cout << "======= MiniZinc predicates =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- A predicate is inlined, not declared. ------------------------------
    // The assertion that matters is the *negative* one: no declare-fun for `p`.
    // A frontend that mapped the predicate onto an uninterpreted function would
    // pass every other check in this file and fail only this.
    {
        const Translation t = run(
            "predicate pos(var int: a) = a > 0;\n"
            "var int: x;\n"
            "constraint pos(x);\n"
            "solve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(> x 0)") || has(smt, "(< 0 x)"));
        assert(!has(smt, "declare-fun pos"));
        assert(!has(smt, "(pos "));
        // ...and the predicate is not a variable of the model either.
        assert(t.report().stats().num_vars == 1);
    }

    // ---- The body is substituted per call site, with its own arguments. -----
    {
        const Translation t = run(
            "predicate pos(var int: a) = a > 0;\n"
            "var int: x;\n"
            "var int: y;\n"
            "constraint pos(x);\n"
            "constraint pos(y);\n"
            "solve satisfy;\n");
        assert(t.ok());
        const std::vector<std::string> a = assertions(t.toSmt2());
        assert(a.size() == 2);
        // Each call constrains ITS OWN argument. The bug this catches is
        // substitution mutating the shared body in place: the first call would
        // rewrite the body's `a` to `x`, and the second would then find no `a`
        // left to replace and re-emit x's constraint under y's call.
        //
        // Checking the assertion lines and not the whole script is the point --
        // `declare-fun y` puts a `y` in the file whatever the constraints say,
        // so a search over the whole script passes even when this is broken.
        const bool one_x = has(a[0], "x") != has(a[1], "x");
        const bool one_y = has(a[0], "y") != has(a[1], "y");
        assert(one_x && one_y);
        assert(t.report().stats().num_constraints == 2);
    }

    // ---- Several parameters, and an argument that is an expression. ---------
    {
        const Translation t = run(
            "predicate between(var int: lo, var int: v, var int: hi) =\n"
            "  lo <= v /\\ v <= hi;\n"
            "var int: x;\n"
            "constraint between(1, x + 1, 10);\n"
            "solve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "+"));
    }

    // ---- Predicates calling predicates. -------------------------------------
    {
        const Translation t = run(
            "predicate pos(var int: a) = a > 0;\n"
            "predicate both(var int: a, var int: b) = pos(a) /\\ pos(b);\n"
            "var int: x;\n"
            "var int: y;\n"
            "constraint both(x, y);\n"
            "solve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(!has(smt, "declare-fun pos"));
        assert(!has(smt, "declare-fun both"));
    }

    // ---- A Bool-parameter predicate. ----------------------------------------
    {
        const Translation t = run(
            "predicate either(var bool: p, var bool: q) = p \\/ q;\n"
            "var bool: a;\n"
            "var bool: b;\n"
            "constraint either(a, b);\n"
            "solve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "or"));
    }

    // ---- Fixed and named-domain parameters. -------------------------------
    {
        const Translation t = run(
            "set of int: row = 1..3;\n"
            "predicate edge(row: r) = r = 1 \\/ r = 3;\n"
            "constraint edge(3);\n"
            "solve satisfy;\n");
        assert(t.ok());
        assert(!has(t.toSmt2(), "declare-fun edge"));
        assert(has(t.toSmt2(), "(assert true)"));
    }
    {
        const Translation outside = run(
            "set of int: row = 1..3;\n"
            "predicate edge(row: r) = r = 1 \\/ r = 3;\n"
            "constraint edge(4);\nsolve satisfy;\n");
        assert(!outside.ok());
        assert(outside.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(outside.diagnostics().all()[0].message, "outside named"));

        const Translation unfixed = run(
            "set of int: row = 1..3;\n"
            "predicate edge(row: r) = r = 1 \\/ r = 3;\n"
            "var row: x;\nconstraint edge(x);\nsolve satisfy;\n");
        assert(!unfixed.ok());
        assert(unfixed.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(unfixed.diagnostics().all()[0].message, "must be fixed"));
    }
    {
        // MiniZinc allows fixed Int arguments to coerce to fixed Float.
        const Translation t = run(
            "predicate ge(float: x, float: y) = x >= y;\n"
            "constraint ge(2, 1.5);\n"
            "solve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(assert true)"));
    }

    // ---- Recursion is refused, not attempted. -------------------------------
    // Inlining a recursive predicate does not terminate. The message has to name
    // recursion: without the `defining_` marker this is reported as an
    // undeclared identifier, which sends a reader looking for a typo.
    {
        const std::string src =
            "predicate loop(var int: a) = loop(a);\n"
            "var int: x;\n"
            "constraint loop(x);\n"
            "solve satisfy;\n";
        assert(rejects(src, ErrorCode::E_UNSUPPORTED_CONSTRUCT));
        const Translation t = run(src);
        assert(has(t.diagnostics().all()[0].message, "recursive"));
    }

    // ---- Parameter shadowing does not leak. ---------------------------------
    // A parameter named like a global must shadow inside the body -- which is
    // what makes the by-name substitution sound -- and must stop shadowing after
    // the item, or the global would be unreachable for the rest of the file.
    {
        // The global and the parameter must differ in SORT, or a leak is
        // unobservable -- which is how the first version of this test passed a
        // probe that deleted the restore entirely. Here the global is Bool and
        // the parameter Int, so a leak leaves `x` recorded as Int and the last
        // constraint stops type-checking.
        const Translation t = run(
            "var bool: x;\n"
            "predicate pos(var int: x) = x > 0;\n"
            "var int: n;\n"
            "constraint pos(n);\n"
            "constraint x;\n"
            "solve satisfy;\n");
        assert(t.ok());
        assert(t.report().stats().num_vars == 2);
    }
    {
        // ...and a parameter whose name was never a global must not linger in
        // scope: a later reference to it is an undeclared identifier, and a leak
        // would silently resolve it to the parameter's sort.
        assert(rejects(
            "predicate pos(var int: tmp) = tmp > 0;\n"
            "var int: x;\nconstraint pos(x) /\\ tmp > 0;\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // The body of a predicate may still mention a global that is not a
        // parameter; substitution must leave it alone.
        const Translation t = run(
            "var int: g;\n"
            "predicate above(var int: a) = a > g;\n"
            "var int: x;\n"
            "constraint above(x);\n"
            "solve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun g"));
        assert(has(smt, "declare-fun x"));
    }

    // ---- What a call must not get away with. --------------------------------
    {
        // Wrong arity.
        assert(rejects(
            "predicate pos(var int: a) = a > 0;\n"
            "var int: x;\nconstraint pos(x, x);\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // Float cannot coerce to Int (Bool can). Checked at the call site: after
        // substitution the parameter is gone, so typeCheck would report against
        // the body's operator with no mention of the call.
        const std::string src =
            "predicate pos(var int: a) = a > 0;\n"
            "var float: b;\nconstraint pos(b);\nsolve satisfy;\n";
        assert(rejects(src, ErrorCode::E_TYPE));
        const Translation t = run(src);
        assert(has(t.diagnostics().all()[0].message, "pos"));
    }
    {
        // A non-Bool body is not a predicate.
        assert(rejects(
            "predicate bad(var int: a) = a + 1;\n"
            "var int: x;\nconstraint bad(x);\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // Redefinition, and a clash with a variable, are both refused: the
        // frontend resolves calls by name from one table.
        assert(rejects(
            "predicate p(var int: a) = a > 0;\n"
            "predicate p(var int: a) = a < 0;\n"
            "var int: x;\nconstraint p(x);\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
        assert(rejects(
            "var int: p;\npredicate p(var int: a) = a > 0;\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // Duplicate parameter names would make substitution ambiguous.
        assert(rejects(
            "predicate p(var int: a, var int: a) = a > 0;\n"
            "var int: x;\nconstraint p(x, x);\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // An explicitly indexed formal must match its actual bounds. The
        // predicate body sees the caller's explicit source index set.
        const Translation t = run(
            "array[2..4] of int: xs = array1d(2..4, [7, 8, 9]);\n"
            "predicate p(array[2..4] of var int: a) = max(index_set(a)) = 4;\n"
            "constraint p(xs);\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "true"));
        assert(rejects(
            "array[1..3] of int: xs = [7, 8, 9];\n"
            "predicate p(array[2..4] of var int: a) = true;\n"
            "constraint p(xs);\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // A polymorphic index type is unified nominally, while each formal
        // retains the actual array's own bounds (the standard-library pattern
        // used by the official IHTC cumulatives predicate).
        const Translation t = run(
            "array[2..4] of int: a = array1d(2..4, [1, 2, 3]);\n"
            "array[9..11] of int: b = array1d(9..11, [4, 5, 6]);\n"
            "predicate p(array[$$E] of var int: x, array[$$E] of var int: y) =\n"
            "  max(index_set(x)) = 4 /\\ min(index_set(y)) = 9;\n"
            "constraint p(a, b);\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "true"));
        assert(rejects(
            "enum E = {A, B};\n"
            "array[E] of int: a = [1, 2];\n"
            "array[1..2] of int: b = [3, 4];\n"
            "predicate p(array[$$I] of var int: x, array[$$I] of var int: y) = true;\n"
            "constraint p(a, b);\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // The `$$T` element type in the standard-library declaration is
        // retained through inlining, so enum tags do not get flattened to
        // plain integers. Reusing $$T for an integer array is a type error.
        const Translation enum_elements = run(
            "enum E = {A, B};\n"
            "array[1..2] of E: xs = [A, B];\n"
            "predicate first(array[$$I] of var $$T: a) = a[1] = A;\n"
            "constraint first(xs);\nsolve satisfy;\n");
        assert(enum_elements.ok());
        assert(has(enum_elements.toSmt2(), "true"));
        assert(rejects(
            "enum E = {A, B};\n"
            "array[1..2] of E: xs = [A, B];\n"
            "array[1..2] of int: ys = [1, 2];\n"
            "predicate same(array[$$I] of var $$T: a, array[$$I] of var $$T: b) = true;\n"
            "constraint same(xs, ys);\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }

    {
        // The same double-dollar type variable can occur as an array element
        // type and another array's index type. MiniZinc unifies these across
        // positions; the enum identity must therefore agree, not merely each
        // position's independent index/element map.
        assert(rejects(
            "enum Machine = {M1, M2}; enum Other = {O1, O2};\n"
            "array[1..2] of var Machine: machines;\n"
            "array[Other] of var int: limits;\n"
            "predicate p(array[int] of var $$M: m, array[$$M] of var int: b) = true;\n"
            "constraint p(machines, limits); solve satisfy;\n",
            ErrorCode::E_TYPE));
        const Translation unified = run(
            "enum Machine = {M1, M2};\n"
            "array[1..2] of var Machine: machines;\n"
            "array[Machine] of var int: limits;\n"
            "predicate p(array[int] of var $$M: m, array[$$M] of var int: b) = true;\n"
            "constraint p(machines, limits); solve satisfy;\n");
        assert(unified.ok());
        // The same actual must still be rejected by a par-array formal. The
        // `var` on the formal controls fixedness; array-ness alone does not.
        assert(rejects(
            "enum Machine = {M1, M2};\n"
            "array[1..2] of var Machine: machines;\n"
            "predicate p(array[int] of $$M: m) = true;\n"
            "constraint p(machines); solve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // `$T` in an index entry captures the complete sequence of axes. Two
        // dimensions are accepted here, while `$$E` remains a single axis.
        const Translation variadic_rank = run(
            "array[1..2, 4..5] of var int: a;\n"
            "predicate p(array[$T] of var int: x) = max(x) >= 0;\n"
            "constraint p(a); solve satisfy;\n");
        assert(variadic_rank.ok());
        // In MiniZinc 2.8.2 `$T` array-index variables constrain rank, while
        // the formal does not replace either caller's nominal index sets.
        const Translation distinct_axes = run(
            "enum Row = {R1, R2}; enum Col = {C1, C2};\n"
            "array[Row, Col] of var int: a; array[Col, Row] of var int: b;\n"
            "predicate p(array[$T] of var int: x, array[$T] of var int: y) =\n"
            "  max(x) >= 0 /\\ max(y) >= 0;\n"
            "constraint p(a, b); solve satisfy;\n");
        assert(distinct_axes.ok());
        assert(rejects(
            "array[1..2, 4..5] of var int: a;\n"
            "array[1..4] of var int: b;\n"
            "predicate p(array[$T] of var int: x, array[$T] of var int: y) = true;\n"
            "constraint p(a, b); solve satisfy;\n",
            ErrorCode::E_TYPE));
        assert(rejects(
            "array[1..2, 4..5] of var int: a;\n"
            "predicate p(array[$$E] of var int: x) = true;\n"
            "constraint p(a); solve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // A single-dollar element variable is general (Bool here), whereas
        // reusing it across actual element types still requires unification.
        const Translation generic_bool = run(
            "array[1..2] of var bool: flags;\n"
            "predicate p(array[int] of var $T: x) = true;\n"
            "constraint p(flags); solve satisfy;\n");
        assert(generic_bool.ok());
        // MiniZinc 2.8.2 accepts a general `$T` across Bool and Int array
        // actuals when the body does not constrain their element type.
        const Translation general_mixed = run(
            "array[1..2] of var bool: flags;\n"
            "array[1..2] of var int: values;\n"
            "predicate p(array[int] of var $T: x, array[int] of var $T: y) = true;\n"
            "constraint p(flags, values); solve satisfy;\n");
        assert(general_mixed.ok());
    }
    {
        // Real array expressions remain finite values with their variable
        // cells. This mirrors cumulatives' decision-array plus concatenated
        // array argument; the body folds over the actual cells after inlining.
        const Translation decision_concat = run(
            "array[4..5] of var int: starts;\n"
            "predicate p(array[$$E] of var int: x, array[$$E] of var int: y) =\n"
            "  max(x) >= 0 /\\ max(y) >= 0;\n"
            "constraint p(starts, starts ++ [starts[4] + 1]);\n"
            "solve satisfy;\n");
        assert(decision_concat.ok());
        assert(has(decision_concat.toSmt2(), "starts"));
        // An array comprehension is also an expression argument and keeps
        // references to the caller's decision array.
        const Translation decision_comprehension = run(
            "array[2..3] of var int: values;\n"
            "predicate p(array[$$E] of var int: x) = max(x) >= 0;\n"
            "constraint p([values[i] + i | i in index_set(values)]);\n"
            "solve satisfy;\n");
        assert(decision_comprehension.ok());
        assert(has(decision_comprehension.toSmt2(), "values"));
    }
    {
        // Predicate arguments are evaluated even when the body ignores them.
        // Inlining must preserve every actual cell's partiality, including
        // under negation; otherwise the total SMT div-by-zero value can make
        // an undefined MiniZinc call appear true or false arbitrarily.
        const std::string prefix =
            "predicate p(array[int] of var int: a) = true;\n"
            "var int: d;\n";
        const Translation positive = run(
            prefix + "constraint p([1 div d]);\n"
            "constraint d = 0;\nsolve satisfy;\n");
        const Translation negative = run(
            prefix + "constraint not p([1 div d]);\n"
            "constraint d = 0;\nsolve satisfy;\n");
        assert(positive.ok());
        assert(negative.ok());
        // MiniZinc 2.8.2/Gecode makes the positive call undefined and therefore
        // inconsistent at d=0, while its negation is satisfiable. The actual
        // quotient need not be emitted because the unused parameter is observed
        // only through its definedness guard.
        const std::string positive_smt = positive.toSmt2();
        const std::string negative_smt = negative.toSmt2();
        assert(has(positive_smt, "(distinct 0 d)"));
        assert(!has(negative_smt, "(distinct 0 d)"));
        assert(has(negative_smt, "(= 0 d)"));
    }
    {
        // A named element domain on a var-array formal narrows the actual
        // cells as a hard type-inst obligation, including below predicate
        // negation. The focused runtime probe checks both calls against Z3.
        const std::string prefix =
            "set of int: allowed = 1..3;\n"
            "array[1..1] of var int: x;\n"
            "predicate p(array[int] of var allowed: a) = true;\n";
        const Translation positive = run(
            prefix + "constraint p(x);\nconstraint x[1] = 7;\nsolve satisfy;\n");
        const Translation negative = run(
            prefix + "constraint not p(x);\nconstraint x[1] = 7;\nsolve satisfy;\n");
        assert(positive.ok());
        assert(negative.ok());
        const std::string positive_smt = positive.toSmt2();
        const std::string negative_smt = negative.toSmt2();
        assert(has(positive_smt, "x"));
        assert(has(negative_smt, "x"));
        // Ensure translation emitted separate domain-related obligations in
        // addition to the call and x=7. The independent solver probe asserts
        // these formulas make both models UNSAT.
        assert(assertions(positive_smt).size() >= 3);
        assert(assertions(negative_smt).size() >= 3);
    }
    {
        // The cumulatives signature uses $$M first for var machine elements
        // and then as the index type of b. Its `[bound | machine in M]` actual
        // is an array expression coerced to M's index type by MiniZinc 2.8.2.
        const Translation cumulative_shape = run(
            "enum Task = {T1, T2}; enum Machine = {M1, M2};\n"
            "array[Task] of var int: s; array[Task] of var int: d;\n"
            "array[Task] of var int: r; array[Task] of var Machine: m;\n"
            "predicate p(array[$$E] of var int: s, array[$$E] of var int: d,\n"
            "  array[$$E] of var int: r, array[$$E] of var $$M: m,\n"
            "  array[$$M] of var int: b) = max(s) >= 0 /\\ max(d) >= 0 /\\ max(r) >= 0 /\\ max(b) >= 0;\n"
            "constraint p(s ++ [s[T1]], [d[i] | i in Task], r ++ [r[T1]],\n"
            "  m ++ [m[T1]], [10 | i in Machine]); solve satisfy;\n");
        assert(cumulative_shape.ok());
    }

    // ---- A zero-parameter predicate is still a predicate. -------------------
    {
        const Translation t = run(
            "var int: x;\n"
            "predicate ok() = x > 0;\n"
            "constraint ok();\n"
            "solve satisfy;\n");
        assert(t.ok());
        assert(!has(t.toSmt2(), "declare-fun ok"));
    }

    // Function calls substitute their own arguments without mutating the
    // shared definition. Inspect assertions, not variable declarations.
    {
        const Translation t = run(
            "function var int: f(var int: a) = a;\n"
            "var int: x;\nvar int: y;\n"
            "constraint f(x) > 0;\nconstraint f(y) < 0;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const auto values = t.parser()->getAssertions();
        VERIFY(values.size() == 2);
        VERIFY(test_bounds::hasVarBound(values, "x", test_bounds::Rel::GT, "0"));
        VERIFY(test_bounds::hasVarBound(values, "y", test_bounds::Rel::LT, "0"));
    }
    {
        VERIFY(rejects(
            "function var int: f(var int: a) = a + 1;\n"
            "constraint f(1, 2) > 0;\nsolve satisfy;\n",
            ErrorCode::E_TYPE));
    }

    // A `test` with a fixed result is accepted as a par-Boolean operation.
    {
        const Translation t = run(
            "test t(int: a) = true;\nconstraint t(1);\nsolve satisfy;\n");
        VERIFY(t.ok());
    }

    std::cout << "======= array-valued par parameters, and `let` =======\n";
    {
        // An ARRAY parameter carries the caller's index set, which the body
        // asks for with `index_set`. A literal is indexed from 1 -- MiniZinc's
        // rule -- and getting that wrong is silent: `ParamArray::lo` defaults
        // to 0, so `[1, 3]` came out indexed 0..1 and `max(index_set(x))` was
        // 1 instead of 2. The model still translated.
        const Translation t = run(
            "predicate p(array [int] of int: x) = max(index_set(x)) = 2;\n"
            "constraint p([1, 3]);\n"
            "solve satisfy;\n");
        assert(t.ok());
        // A true constant, not a false one: the assertion is that the index
        // set is 1..2 and not 0..1.
        assert(has(t.toSmt2(), "true"));
        assert(!has(t.toSmt2(), "(assert false)"));
    }
    {
        // A cell of an array argument, read by the body.
        const Translation t = run(
            "var 1..9: y;\n"
            "predicate p(array [int] of int: x) = y = x[2];\n"
            "constraint p([4, 7]);\n"
            "solve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "7"));
        assert(!has(t.toSmt2(), "4"));   // x[1], which was not asked for
    }
    {
        // `let` declaring a decision array, and the property that matters:
        // ONE ARRAY PER CALL. `let` is opened once per call, and an
        // implementation that declared the array once and shared it would
        // constrain the two calls to agree -- a WRONG ANSWER, not a refusal,
        // and one no "did it translate" check can see.
        const Translation t = run(
            "set of int: col = 1..5;\n"
            "array [1..2] of var bool: a;\n"
            "predicate p(int: r) =\n"
            "    let { int: n = 1, array [1..n] of var col: s } in (s[1] > r);\n"
            "constraint p(1);\n"
            "constraint p(2);\n"
            "solve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Two distinct arrays, named apart by the serial.
        assert(has(smt, "s@let0"));
        assert(has(smt, "s@let1"));
        // ...and each call constrains its own.
        const std::vector<std::string> lines = assertions(smt);
        std::size_t with0 = 0, with1 = 0;
        for (const std::string& l : lines) {
            if (has(l, "s@let0")) { ++with0; }
            if (has(l, "s@let1")) { ++with1; }
        }
        assert(with0 > 0 && with1 > 0);
        // The element domain reaches the cells: `var col` is 1..5, and without
        // these the array is unconstrained and the model admits answers the
        // source excludes.
        assert(has(smt, "(select s@let0 1)"));
        assert(has(smt, ">= (select s@let0 1) 1") || has(smt, "(<= 1 (select s@let0 1))"));
    }
    {
        // A `let` name is scoped to its body. After the call it means whatever
        // it meant before -- here, nothing, so the model is refused rather than
        // silently reading the let's array.
        assert(rejects(
            "set of int: col = 1..5;\n"
            "predicate p(int: r) =\n"
            "    let { int: n = 1, array [1..n] of var col: s } in (s[1] > r);\n"
            "constraint p(1);\n"
            "constraint s[1] > 0;\n"
            "solve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    for (int argument : {0, 1}) {
        // Fixed Bool locals are supported. Check their value and restoration
        // of the outer binding, rather than retaining the old refusal test.
        const Translation t = run(
            "bool: b = false;\n"
            "predicate p(int: r) = let { bool: b = r > 0 } in b;\n"
            "constraint p(" + std::to_string(argument) + ");\n"
            "constraint not b;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(assert false)") == (argument == 0));
    }
    {
        VERIFY(rejects(
            "predicate p(int: r) = let { bool: b = 7 } in b;\n"
            "constraint p(1);\n"
            "solve satisfy;\n",
            ErrorCode::E_TYPE));
    }
    {
        // MiniZinc permits generators over an array whose cells are fixed
        // sets. The generator binds each whole set value; max(si) must not
        // reinterpret si as an integer, use the array index, or expand set
        // members as generator iterations.
        const Translation t = run(
            "set of int: si = {99};\n"
            "array[3..4] of set of int: sets = array1d(3..4, [{0,3}, {0,4}]);\n"
            "constraint sum([max(si) | si in sets]) = 7;\n"
            "constraint max(si) = 99;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        const auto first_true = smt.find("(assert true)");
        VERIFY(first_true != std::string::npos);
        VERIFY(smt.find("(assert true)", first_true + 1) != std::string::npos);
        VERIFY(!has(smt, "__mzn_fixed_set_generator_"));
    }
    {
        // A wrong expected sum remains contradictory, proving that the
        // preceding successful fold did not merely erase the constraints.
        const Translation t = run(
            "array[3..4] of set of int: sets = array1d(3..4, [{0,3}, {0,4}]);\n"
            "constraint sum([max(si) | si in sets]) = 8;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(assert false)"));
    }
    {
        // Source-shaped reduction of gt-sort's pipeline: reverse/sort an
        // integer array, build a fixed set array by comprehension, then fold
        // over the array of sets. Duplicate `3` inputs must remain two cells.
        const Translation t = run(
            "array[int] of int: c = [3,-1,3,0];\n"
            "array[int] of set of int: s = [{0,ci} | ci in reverse(sort(c))];\n"
            "constraint sum([max(si) | si in s]) = 6;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(assert true)"));
        VERIFY(!has(t.toSmt2(), "__mzn_fixed_set_generator_"));
    }
    {
        // Array generators preserve duplicate cells, and a fixed-set
        // membership/fold consumes each selected cell's exact value.
        const Translation t = run(
            "array[1..2] of set of int: sets = [{1}, {1}];\n"
            "int: cardinalities = sum([card(si) | si in sets]);\n"
            "int: hits = sum([if 1 in si then 1 else 0 endif | si in sets]);\n"
            "constraint cardinalities = 2 /\\ hits = 2;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(assert true)"));
        VERIFY(!has(smt, "__mzn_fixed_set_generator_"));
    }
    {
        // Set-valued generator bindings remain lexical: the outer fixed set
        // with the same name is restored after the comprehension.
        const Translation t = run(
            "set of int: si = {99};\n"
            "array[1..2] of set of int: sets = [{2}, {5}];\n"
            "constraint sum([max(si) | si in sets]) = 7;\n"
            "constraint max(si) = 99;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        const auto first_true = smt.find("(assert true)");
        VERIFY(first_true != std::string::npos);
        VERIFY(smt.find("(assert true)", first_true + 1) != std::string::npos);
        VERIFY(!has(smt, "__mzn_fixed_set_generator_"));
    }
    {
        // Marker reuse is valid only while the lexical array binding still
        // denotes the same fixed cells. The same source name is rebound to
        // different values, and then to an empty array, across nested scopes.
        // Each fold must use its own current binding rather than stale cached
        // marker values from the earlier scope.
        const Translation t = run(
            "constraint let { array[1..1] of set of int: sets = [{2}] } in "
            "sum([max(si) | si in sets]) = 2;\n"
            "constraint let { array[1..1] of set of int: sets = [{5}] } in "
            "sum([max(si) | si in sets]) = 5;\n"
            "constraint let { array[1..0] of set of int: sets = [] } in "
            "sum([1 | si in sets]) = 0;\n"
            "constraint let { array[1..1] of set of int: sets = [{7}] } in "
            "sum([max(si) | si in sets]) = 7;\n"
            "solve satisfy;\n");
        if (!t.ok()) {
            for (const auto& diagnostic : t.diagnostics().all()) {
                std::cerr << diagnostic.message << "\n";
            }
        }
        VERIFY(t.ok());
        const auto lines = assertions(t.toSmt2());
        VERIFY(lines.size() == 4);
        for (const auto& line : lines) { VERIFY(line == "(assert true)"); }
        VERIFY(!has(t.toSmt2(), "__mzn_fixed_set_generator_"));
    }
    {
        // Parameter logarithm rounding uses exact integer-power comparisons,
        // so an approximation cannot cross a power-of-base boundary.
        for (const auto& sample : std::vector<std::pair<std::string, int>>{
                 {"ceil(log2(8))", 3}, {"ceil(log2(9))", 4},
                 {"floor(log2(8))", 3}, {"floor(log2(9))", 3},
                 {"ceil(log(10,99))", 2}, {"ceil(log(10,100))", 2},
                 {"ceil(log(10,101))", 3}, {"floor(log(10,99))", 1},
                 {"floor(log(10,100))", 2}, {"floor(log(10,101))", 2},
                 {"ceil(log2(1))", 0}}) {
            const Translation t = run(
                "int: bound = " + sample.first + ";\n"
                "constraint bound = " + std::to_string(sample.second) + ";\n"
                "solve satisfy;\n");
            VERIFY(t.ok());
            const auto lines = assertions(t.toSmt2());
            VERIFY(lines.size() == 1);
            VERIFY(lines.front() == "(assert true)");
        }
        VERIFY(rejects(
            "int: bound = ceil(log2(0));\nsolve satisfy;\n", ErrorCode::E_TYPE));
        const Translation negated_constant = run(
            "int: n = 2;\n"
            "constraint not (ceil(log2(n)) = 2);\n"
            "solve satisfy;\n");
        VERIFY(negated_constant.ok());
        VERIFY(assertions(negated_constant.toSmt2()).front() == "(assert true)");
        const Translation negated_partial = run(
            "constraint not (ceil(log2(1 div 0)) = 0);\nsolve satisfy;\n");
        VERIFY(!negated_partial.ok());
        VERIFY(rejects(
            "var int: n; int: bound = ceil(log2(n));\nsolve satisfy;\n",
            ErrorCode::E_UNSUPPORTED_CONSTRUCT));
        const Translation false_let_arithmetic = run(
            "int: n = ceil(let { constraint false; } in (1.0 + 0.5));\n"
            "constraint n = 2;\nsolve satisfy;\n");
        VERIFY(!false_let_arithmetic.ok());
        VERIFY(false_let_arithmetic.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        const Translation true_let_arithmetic = run(
            "int: n = ceil(let { constraint true; } in (1.0 + 0.5));\n"
            "constraint n = 2;\nsolve satisfy;\n");
        VERIFY(true_let_arithmetic.ok());
        VERIFY(assertions(true_let_arithmetic.toSmt2()).front() == "(assert true)");
        const Translation exact_division = run(
            "array[int] of int: c = [1,2,3,4,5,6,7,8,9,10,11,12,13];\n"
            "int: pairs = ceil(length(c) / (2^2));\n"
            "constraint pairs = 4;\nsolve satisfy;\n");
        VERIFY(exact_division.ok());
        VERIFY(assertions(exact_division.toSmt2()).front() == "(assert true)");
        const Translation zero_division = run(
            "int: pairs = ceil(3 / 0);\nsolve satisfy;\n");
        VERIFY(!zero_division.ok());
        VERIFY(zero_division.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }
    {
        // Array cells declared as finite decision sets retain both their set
        // sort and their per-cell element-domain restriction.
        const Translation allowed = run(
            "array[2..3] of var set of 1..4: choices;\n"
            "constraint 4 in choices[2];\n"
            "constraint card(choices[3]) >= 0;\n"
            "solve satisfy;\n");
        VERIFY(allowed.ok());
        VERIFY(!has(allowed.toSmt2(), "(forall "));
        for (int cell : {2, 3}) {
            VERIFY(finiteDomainEquation(allowed.toSmt2(),
                "(select choices " + std::to_string(cell) + ")",
                "set.insert 1 2 3 4"));
        }
        VERIFY(has(allowed.toSmt2(), "set.member"));
        const Translation excluded = run(
            "array[2..3] of var set of 1..4: choices;\n"
            "constraint 5 in choices[2];\n"
            "solve satisfy;\n");
        VERIFY(excluded.ok());
        VERIFY(!has(excluded.toSmt2(), "(forall "));
        VERIFY(finiteDomainEquation(excluded.toSmt2(), "(select choices 2)",
                                   "set.insert 1 2 3 4"));
        VERIFY(has(excluded.toSmt2(), "set.member"));
    }
    {
        // A set-array binder can itself be a source for a nested generator.
        // This is the domain expression used by official gt-sort: min over
        // every element of every fixed set, then a bounded decision set.
        const Translation t = run(
            "array[1..2] of set of int: sets = [{0,3}, {0,4}];\n"
            "int: least = min(si in sets, a in si)(a);\n"
            "array[1..2] of var set of min(si in sets, a in si)(a)..4: choices;\n"
            "constraint least = 0;\n"
            "constraint 3 in choices[1];\n"
            "solve satisfy;\n");
        if (!t.ok()) {
            for (const auto& diagnostic : t.diagnostics().all()) {
                std::cerr << diagnostic.message << "\n";
            }
        }
        VERIFY(t.ok());
        VERIFY(!has(t.toSmt2(), "(forall "));
        VERIFY(has(t.toSmt2(), "set.inter"));
        VERIFY(has(t.toSmt2(), "set.insert 0 1 2 3 4"));
    }
    {
        // A multidimensional local decision array with an arithmetic domain
        // keeps the range restriction on every flattened cell.
        const Translation t = run(
            "constraint let { int: pairs = 2; "
            "array[1..pairs,1..2] of var 1..(2*pairs): y; } in y[1,1] = 1;\n"
            "solve satisfy;\n");
        if (!t.ok()) {
            for (const auto& diagnostic : t.diagnostics().all()) {
                std::cerr << diagnostic.message << "\n";
            }
        }
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        for (int cell = 0; cell < 4; ++cell) {
            const std::string selected = "(select y@let0 " + std::to_string(cell) + ")";
            VERIFY(has(smt, "(>= " + selected + " 1)"));
            VERIFY(has(smt, "(<= " + selected + " 4)"));
        }
    }
    {
        // A tuple-valued comprehension carries a distinct local decision
        // array per outer row. Iterating the array-valued tuple field must
        // visit those selected cells in order and keep their declarations.
        const Translation t = run(
            "array[int] of int: c = [1,2,3,4];\n"
            "set of int: L = 1..(1 + ceil(log2(length(c))));\n"
            "any: y_pairs = [\n"
            "  let { int: pairs = ceil(length(c) / (2^i));\n"
            "        array[1..pairs,1..2] of var 1..(2*pairs): y; }\n"
            "  in (pairs: pairs, y: y) | i in L diff {max(L)}];\n"
            "any: y_vars = [v | r in y_pairs, v in r.y];\n"
            "constraint forall(i in L diff {max(L)})("
            "let { any: y = y_pairs[i].y; } in alldifferent(y));\n"
            "solve satisfy;\n");
        if (!t.ok()) {
            for (const auto& diagnostic : t.diagnostics().all()) {
                std::cerr << errorCodeName(diagnostic.code) << " "
                          << diagnostic.loc.file << ":" << diagnostic.loc.line << ":"
                          << diagnostic.loc.column << " " << diagnostic.message << "\n";
            }
        }
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "y@let"));
        VERIFY(has(smt, "(select"));
        VERIFY(has(smt, "(<= (select y@let"));
    }
    {
        // Equality between a decision set-array slice and a fixed set-array
        // value is extensional: each cell must have exactly the listed members.
        const Translation t = run(
            "array[1..2,1..2] of var set of 0..4: choices;\n"
            "array[1..2] of set of int: expected = [{0,2}, {1,3}];\n"
            "constraint choices[1,..] = expected;\n"
            "solve satisfy;\n");
        if (!t.ok()) {
            for (const auto& diagnostic : t.diagnostics().all()) {
                std::cerr << diagnostic.message << "\n";
            }
        }
        VERIFY(t.ok());
        VERIFY(!has(t.toSmt2(), "(forall "));
        VERIFY(has(t.toSmt2(), "set.inter"));
        VERIFY(has(t.toSmt2(), "set.insert 0 1 2 3 4"));
        VERIFY(has(t.toSmt2(), "set.insert 0 2"));
        VERIFY(has(t.toSmt2(), "set.insert 1 3"));
    }
    {
        // A typed local decision-set alias in a let keeps the selected source
        // array cell as a set expression instead of treating `set` as a value.
        const Translation t = run(
            "array[1..1] of var set of 0..3: choices;\n"
            "constraint let { var set of int: a = choices[1]; } in 2 in a;\n"
            "solve satisfy;\n");
        if (!t.ok()) {
            for (const auto& diagnostic : t.diagnostics().all()) {
                std::cerr << errorCodeName(diagnostic.code) << " "
                          << diagnostic.loc.file << ":" << diagnostic.loc.line << ":"
                          << diagnostic.loc.column << " " << diagnostic.message << "\n";
            }
        }
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "set.member"));
    }
    {
        // `ub(a)` ranges over the declared finite universe of a decision set,
        // not the set's unknown current members: 0+1+2+3 is exactly six.
        const auto model = [](int expected) {
            return "array[1..1] of var set of 0..3: choices;\n"
                "constraint let { var set of int: a = choices[1]; } in "
                "sum([v | v in ub(a)]) = " + std::to_string(expected) + ";\n"
                "solve satisfy;\n";
        };
        const Translation sat = run(model(6));
        if (!sat.ok()) {
            for (const auto& diagnostic : sat.diagnostics().all()) {
                std::cerr << errorCodeName(diagnostic.code) << " "
                          << diagnostic.loc.file << ":" << diagnostic.loc.line << ":"
                          << diagnostic.loc.column << " " << diagnostic.message << "\n";
            }
        }
        VERIFY(sat.ok());
        VERIFY(has(sat.toSmt2(), "(assert true)"));
        const Translation unsat = run(model(7));
        if (!unsat.ok()) {
            for (const auto& diagnostic : unsat.diagnostics().all()) {
                std::cerr << errorCodeName(diagnostic.code) << " "
                          << diagnostic.loc.file << ":" << diagnostic.loc.line << ":"
                          << diagnostic.loc.column << " " << diagnostic.message << "\n";
            }
        }
        VERIFY(unsat.ok());
        VERIFY(has(unsat.toSmt2(), "(assert false)"));
    }
    {
        // The empty set literal is typed by its decision-set equality peer.
        const Translation t = run(
            "array[1..1] of var set of 0..3: choices;\n"
            "constraint choices[1] = {};\n"
            "solve satisfy;\n");
        if (!t.ok()) {
            for (const auto& diagnostic : t.diagnostics().all()) {
                std::cerr << errorCodeName(diagnostic.code) << " "
                          << diagnostic.loc.file << ":" << diagnostic.loc.line << ":"
                          << diagnostic.loc.column << " " << diagnostic.message << "\n";
            }
        }
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "set.empty"));
    }

    std::cout << "All MiniZinc predicate tests passed." << std::endl;
    return 0;
}
