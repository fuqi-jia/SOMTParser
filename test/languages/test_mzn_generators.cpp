// Generator expressions, parameter arrays, and the bool-to-int coercion.
//
// These are what the libminizinc corpus failed on after the lexical and
// item-level gaps were closed. All three are unrolled or folded at PARSE time,
// which is exact and needs no HIR surface: a generator's index sets are
// parameters, so every one is a known integer range before the body is read,
// and what MiniZinc's own flattening produces is the same conjunction.
//
// The assertions are semantic. The builders fold constants and reorder
// commutative operands (CLAUDE.md invariant 2), so counting `select` terms and
// checking which indices appear says what the model means; matching emitted
// text would pin what the caller does not choose.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0;
    for (std::size_t i = hay.find(needle); i != std::string::npos;
         i = hay.find(needle, i + needle.size())) {
        ++n;
    }
    return n;
}

Translation run(const std::string& src, const std::string& profile = "ground") {
    Lang::SourceUnit u;
    u.main_path = "t.mzn";
    u.display_name = "t.mzn";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "minizinc";
    opts.profile_id = profile;
    return translate(u, opts);
}

std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    assert(false && "no error recorded");
    return "";
}

const char* kArr = "int: n = 3;\narray[1..n] of var 1..n: q;\n";

} // namespace

int main() {
    std::cout << "======= MiniZinc: generators, parameter arrays, coercion =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- 1. Generator calls -----------------------------------------------
    {
        const Translation t = run(kArr + std::string(
            "constraint forall(i in 1..n)(q[i] > 0);\nsolve satisfy;\n"));
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // One conjunct per index, and exactly the declared index set.
        assert(has(smt, "(> (select q 1) 0)"));
        assert(has(smt, "(> (select q 3) 0)"));
        assert(!has(smt, "(select q 4)"));
        assert(!has(smt, "(select q 0)"));
    }
    {
        // **The dependent-bound case, which is the whole reason generators are
        // re-parsed per binding rather than evaluated once.** `j in i+1..n`
        // is not one range but one per value of i; evaluating it once gives
        // `j in 2..n` for every i and produces `q[2] != q[2]` -- an UNSAT
        // constraint from a satisfiable model, with no diagnostic.
        const Translation t = run(kArr + std::string(
            "constraint forall(i in 1..n, j in i+1..n)(q[i] != q[j]);\n"
            "solve satisfy;\n"));
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Three unordered pairs from three elements, and no self-comparison.
        assert(count(smt, "distinct") + count(smt, "(not (=") == 3);
        for (const char* self : {"(select q 1) (select q 1)",
                                 "(select q 2) (select q 2)",
                                 "(select q 3) (select q 3)"}) {
            assert(!has(smt, self));
        }
    }
    {
        // `where` is evaluated, not required to be a literal: `i mod 2 = 0` is
        // arithmetic on a bound variable and folds per binding.
        const Translation t = run(
            "int: n = 4;\narray[1..n] of var 0..9: a;\n"
            "constraint forall(i in 1..n where i mod 2 = 0)(a[i] = 0);\n"
            "solve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= 0 (select a 2))") || has(smt, "(= (select a 2) 0)"));
        assert(has(smt, "(= 0 (select a 4))") || has(smt, "(= (select a 4) 0)"));
        assert(!has(smt, "(select a 1)") || !has(smt, "(= 0 (select a 1))"));
    }
    {
        // A decision-dependent filter stays in the formula. Its truth cannot
        // be decided by the parser; each universal body is guarded instead.
        const Translation t = run(
            "array[1..2] of var 0..9: a;\n"
            "constraint forall(i in 1..2 where a[i] > 0)(a[i] = 1);\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "ite"));
    }
    {
        // An empty index set is the operator's unit, not an error.
        const Translation t = run(
            "int: n = 0;\narray[1..2] of var 0..1: a;\n"
            "constraint forall(i in 1..n)(a[i] = 1);\n"
            "constraint a[1] = 0;\nsolve satisfy;\n");
        assert(t.ok());
        // The `forall` contributed nothing, and the constraint AFTER it -- the
        // one whose tokens follow the generator body -- survived. A generator
        // that mispositioned the lexer would lose it.
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= 0 (select a 1))") || has(smt, "(= (select a 1) 0)"));
    }
    {
        // A nested generator may reuse the name; the inner binding wins and the
        // outer one comes back.
        const Translation t = run(
            "array[1..4] of var 0..9: a;\n"
            "constraint forall(i in 1..2)(forall(i in 3..4)(a[i] = 7));\n"
            "constraint forall(i in 1..2)(a[i] = 5);\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(select a 3)") && has(smt, "(select a 4)"));
        assert(has(smt, "(select a 1)") && has(smt, "(select a 2)"));
    }
    {
        // sum and product fold to their operators, with the right units.
        const Translation t = run(kArr + std::string(
            "constraint sum(i in 1..n)(q[i]) = 6;\nsolve satisfy;\n"));
        assert(t.ok());
        assert(count(t.toSmt2(), "select q") >= 3);
    }
    {
        const Translation t = run(
            "int: n = 0;\nvar 0..9: x;\n"
            "constraint sum(i in 1..n)(x) = 0;\nsolve satisfy;\n");
        assert(t.ok());          // empty sum is 0, so `0 = 0` holds
    }

    // ---- 1b. Whole-array folds: `sum(x)` is `sum(i in index_set(x))(x[i])` --
    // the stdlib's array[$T] overloads (handbook 4.2.2.7), which the
    // natural-language route emits as readily as the generator form. ---------
    {
        // A decision array folds one select per cell over the SOURCE index,
        // so the emitted text reads like the model.
        const Translation t = run(kArr + std::string(
            "constraint sum(q) <= 6;\nsolve satisfy;\n"));
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(select q 1)") && has(smt, "(select q 2)")
               && has(smt, "(select q 3)"));
        assert(!has(smt, "(select q 0)") && !has(smt, "(select q 4)"));
    }
    {
        // A parameter array folds its VALUES: c is data, so no select exists
        // to emit and the sum is the literal 6 at parse time.
        const Translation t = run(
            "array[1..3] of int: c = [1, 2, 3];\nvar 0..9: x;\n"
            "constraint sum(c) + x = 7;\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(!has(smt, "select"));
        assert(has(smt, "(+ 6 x)") || has(smt, "(+ x 6)"));
    }
    {
        // Two or more dimensions fold over the FLAT cell space -- the same
        // row-major 0..cells-1 bounds alldifferent(a) already uses.
        const Translation t = run(
            "array[1..2, 1..2] of var 1..9: g;\n"
            "constraint sum(g) <= 30;\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        for (const char* cell : {"(select g 0)", "(select g 1)",
                                 "(select g 2)", "(select g 3)"}) {
            assert(has(smt, cell));
        }
        assert(!has(smt, "(select g 4)"));
    }
    {
        // product and the Boolean aggregations share the fold; the empty
        // array's unit is the operator's identity, not an error.
        const Translation t = run(kArr + std::string(
            "constraint product(q) = 6;\nsolve satisfy;\n"));
        assert(t.ok());
        assert(count(t.toSmt2(), "select q") >= 3);
    }
    {
        const Translation t = run(
            "array[1..3] of var bool: b;\n"
            "constraint forall(b);\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(select b 1)") && has(smt, "(select b 3)"));
    }
    {
        const Translation t = run(
            "array[1..2] of var bool: b;\n"
            "constraint exists(b);\nsolve satisfy;\n");
        assert(t.ok());
    }
    {
        const Translation t = run(
            "array[1..2] of bool: bs = [true, true];\nvar 0..9: x;\n"
            "constraint forall(bs) -> x = 4;\nsolve satisfy;\n");
        assert(t.ok());          // forall over data folds to true at parse time
    }
    {
        const Translation t = run(
            "array[1..0] of int: e = [];\nvar 0..9: x;\n"
            "constraint sum(e) = x;\nsolve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= 0 x)") || has(smt, "(= x 0)"));
    }
    {
        // Numeric array signatures admit MiniZinc's Bool-to-Int coercion.
        const Translation t = run(
            "array[1..2] of var bool: b;\n"
            "constraint sum(b) > 0;\nsolve satisfy;\n");
        assert(t.ok());
    }
    {
        // Int-to-Bool is not an automatic coercion.
        const Translation t = run(kArr + std::string(
            "constraint forall(q);\nsolve satisfy;\n"));
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }
    {
        // A scalar is not the one array the aggregation takes.
        const Translation t = run(
            "var 0..9: x;\nconstraint sum(x) > 0;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(firstError(t), "not an array"));
    }
    {
        const Translation t = run(
            "constraint sum(nope) > 0;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "undeclared identifier 'nope'"));
    }
    {
        // A parameter IS declared; the diagnostic must not claim otherwise.
        const Translation t = run(kArr + std::string(
            "constraint sum(n) > 0;\nsolve satisfy;\n"));
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(!has(firstError(t), "undeclared"));
    }
    {
        // `sum([1, 2])` is legal MiniZinc -- the literal coerces to the one
        // array argument. This case asserted the REFUSAL until 2026-09-20,
        // which is a different kind of claim: it pinned a limitation of this
        // subset rather than a property of the language, so lifting the
        // limitation had to move the test with it. Kept here, inverted, rather
        // than deleted -- the row is what says the probe below still tells a
        // literal argument apart from a generator clause. The feature itself
        // is covered in test_mzn_fold_arguments.cpp, which checks it against
        // the generator form differentially.
        const Translation t = run(
            "constraint sum([1, 2, 3]) = 6;\nsolve satisfy;\n");
        assert(t.ok());
    }
    {
        // The probe is a save/restore: a name followed by `in` (not ')') goes
        // back to the generator path unchanged -- two generator calls in one
        // expression still fold per binding.
        const Translation t = run(kArr + std::string(
            "constraint sum(i in 1..n)(q[i]) + sum(j in 1..2)(q[j] * 2) = 12;\n"
            "solve satisfy;\n"));
        assert(t.ok());
        assert(has(t.toSmt2(), "(select q 3)"));
    }
    {
        // The bundled fixtures behave as their directory promises.
        Lang::SourceUnit ok;
        ok.main_path = "languages/minizinc/instances/ok/whole_array_fold.mzn";
        assert(translate(ok).ok());
        ok.main_path = "languages/minizinc/instances/ok/sum_over_bool_array.mzn";
        assert(translate(ok).ok());
        Lang::SourceUnit bad;
        bad.main_path =
            "languages/minizinc/instances/reject/sum_over_string_array.mzn";
        const Translation t = translate(bad);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    // ---- 2. alldifferent, all three shapes --------------------------------
    {
        // The declared-array form still works, and still goes through the
        // profile: the encoding is decompose-globals', not the frontend's.
        const Translation t = run(kArr + std::string(
            "constraint alldifferent(q);\nsolve satisfy;\n"));
        assert(t.ok());
        bool found = false;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "alldifferent") { found = true; }
        }
        assert(found);
    }
    {
        // An array LITERAL: there is no declared array to name.
        const Translation t = run(kArr + std::string(
            "constraint alldifferent([q[1], q[3]]);\nsolve satisfy;\n"));
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(select q 1)") && has(smt, "(select q 3)"));
    }
    {
        // A GENERATOR: the terms are computed, so the list shape is the only
        // one that fits -- and it must still be a global, so the profile keeps
        // choosing the encoding.
        const Translation t = run(kArr + std::string(
            "constraint alldifferent(i in 1..n)(q[i] + i);\nsolve satisfy;\n"));
        assert(t.ok());
        bool distinct = false;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "alldifferent" && e.strategy == "alldifferent-distinct") {
                distinct = true;
            }
        }
        // Recorded as distinct under BOTH styles, because an explicit list has
        // no index set to quantify over -- reporting "quantified" would name an
        // encoding nobody built.
        assert(distinct);
    }
    {
        const Translation t = run(kArr + std::string(
            "constraint alldifferent(i in 1..n)(q[i] + i);\nsolve satisfy;\n"),
                                  "quantified");
        assert(t.ok());
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "alldifferent") {
                assert(e.strategy == "alldifferent-distinct");
            }
        }
    }
    {
        // The shape is chosen by the first argument's SORT, not by the argument
        // count, and this is the case that tells the two apart. Three Boolean
        // terms are a LIST that is ill-sorted; a count-based dispatch would
        // read them as `(array, lo, hi)` and report "alldifferent's lower index
        // bound is Bool" -- naming an index bound the author never wrote.
        //
        // The encoding comes out right either way, because decompose-globals
        // makes its own sort-based decision. Only the message differs, which is
        // why it is the message that is asserted.
        const Translation t = run(
            "var bool: a;\nvar bool: b;\nvar bool: c;\n"
            "constraint alldifferent([a, b, c]);\nsolve satisfy;\n");
        assert(!t.ok());
        const std::string m = firstError(t);
        assert(has(m, "argument 1") || has(m, "first argument"));
        assert(!has(m, "index bound"));
    }
    {
        // One term is vacuously all-different; the checker's list shape needs
        // two, so the frontend must not hand it a one-argument global.
        const Translation t = run(kArr + std::string(
            "constraint alldifferent([q[1]]);\nsolve satisfy;\n"));
        assert(t.ok());
    }

    // ---- 3. Parameter arrays ----------------------------------------------
    {
        // Data, not decisions: `w[i]` is the value, so a parameter array works
        // wherever a number does.
        const Translation t = run(
            "int: n = 3;\narray[1..n] of int: w = [3, 1, 4];\n"
            "array[1..n] of var 0..1: x;\n"
            "constraint sum(i in 1..n)(w[i] * x[i]) <= 5;\n"
            "solve maximize sum(i in 1..n)(w[i] * x[i]);\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // w is not a variable of the model.
        assert(!has(smt, "declare-fun w"));
        assert(t.report().stats().num_vars == 1);      // x alone
        // The coefficients reached the arithmetic.
        assert(has(smt, "(* 3 (select x 1))"));
        assert(has(smt, "(* 4 (select x 3))"));
    }
    {
        // Length is checked against the declared index set. A short list would
        // leave w[3] undefined, and an SMT-LIB array being TOTAL means
        // "undefined" reads as "unconstrained" rather than as an error.
        const Translation t = run("array[1..3] of int: w = [1,2];\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "indexes differ"));
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }
    {
        const Translation t = run(
            "array[1..2] of int: w = [1,2];\nvar 0..9: x;\n"
            "constraint x = w[5];\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "outside"));
    }
    {
        // No value means a .dzn is needed; refused rather than defaulted.
        const Translation t = run("array[1..2] of int: w;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), ".dzn"));
    }

    // ---- 4. bool-to-int coercion ------------------------------------------
    {
        // MiniZinc coerces bool to int in an ARITHMETIC context (the
        // specification lists it among the automatic coercions), so `x + b` is
        // legal and b contributes 0 or 1.
        const Translation t = run(
            "var 0..10: x;\nvar bool: b;\n"
            "constraint x + b >= 3;\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "ite b 1 0"));
    }
    {
        // bool2int is MiniZinc's explicit spelling of the same thing.
        const Translation t = run(
            "var 0..10: x;\nvar bool: b;\n"
            "constraint x + bool2int(b) >= 3;\nsolve satisfy;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "ite b 1 0"));
    }
    {
        // ...and it is a coercion, not a cast: an Int argument is a type error.
        const Translation t = run("var 0..9: x;\nconstraint bool2int(x) = 1;\n"
                                  "solve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "not Bool"));
    }
    {
        // The coercion must NOT reach a Boolean context. `=` on two Booleans is
        // equivalence, and turning it into integer arithmetic would translate a
        // model nobody wrote.
        const Translation t = run("var bool: a;\nvar bool: b;\n"
                                  "constraint a = b;\nsolve satisfy;\n");
        assert(t.ok());
        assert(!has(t.toSmt2(), "ite"));
    }
    {
        // There is no int-to-bool coercion, so this stays a type error --
        // which is what keeps the coercion from swallowing genuine ones.
        const Translation t = run("var int: x;\nconstraint x /\\ true;\n"
                                  "solve satisfy;\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    std::cout << "All MiniZinc generator tests passed." << std::endl;
    return 0;
}
