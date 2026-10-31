// The CryptoLine frontend, and the six obligations docs/languages/cryptoline.md
// wrote down before it existed.
//
// The one that governs everything: **the width is the arithmetic, not an
// annotation on it.** Every variable declares a bit width and a signedness and
// every operation wraps at that width, so a translation to unbounded Int is not
// a relaxation -- it is a different arithmetic, one in which `mull` never
// overflows and the carry outputs the program depends on are always zero.
//
// And the signedness declaration decides a conversion whose two readings are
// indistinguishable downstream. A postcondition's algebraic half is integer
// arithmetic over the VALUES of bit-vectors, so each operand is lifted to Int --
// `bv2nat` for a `uintN` variable, `bv2int` for a `sintN` one. The two read the
// same bits as [0, 2^w) and as [-2^(w-1), 2^(w-1)); the wrong one shifts every
// negative value by exactly 2^w, and both are BitVec -> Int, so nothing
// downstream can tell. The test for it is a single file holding one variable of
// each kind, so neither lift can be the frontend's default.
//
// Two obligations are about a value the translation can silently lose: the carry
// that `adds` produces as data, and the `x = hi * 2^n + lo` identity that
// `split` must ASSERT rather than assume. Both leave a variable declared and
// undefined if missed, and a postcondition about an undefined variable is
// trivially satisfiable -- the verification passes and means nothing.
//
// `cut` is refused, and it is the one refusal that is about the SHAPE of the
// contract rather than about coverage: it makes one instance into several
// queries, chained by their pre- and postconditions, and a ConstraintModel is
// one.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/cryptoline.h"
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

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.cl";
    u.display_name = "t.cl";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "cryptoline";
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "cryptoline";
    return translate(u, opts);
}

Translation runFile(const std::string& path, const std::string& check_index) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "cryptoline";
    opts.parse.options["check_index"] = check_index;
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= CryptoLine frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* c = Lang::LanguageRegistry::instance().byId("cryptoline");
    assert(c != nullptr);
    assert(c->extensions().size() == 1 && c->extensions()[0] == ".cl");

    // ---- The width is the arithmetic. --------------------------------------
    {
        const Translation t = runFile("languages/cryptoline/instances/ok/carry.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Variables are bit-vectors at their declared width, not Ints.
        assert(has(smt, "declare-fun x () (_ BitVec 8)"));
        assert(!has(smt, "declare-fun x () Int"));
        // And the operations are bit-vector operations, so they wrap.
        assert(has(smt, "bvadd"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Obligation: the carry is data, produced not discarded. ------------
    {
        const Translation t = runFile("languages/cryptoline/instances/ok/carry.cl");
        const std::string smt = t.toSmt2();
        // The carry is a 1-bit variable...
        assert(has(smt, "declare-fun c () (_ BitVec 1)"));
        // ...DEFINED as the top bit of the one-wider sum. Declaring it and
        // leaving it free would satisfy the line above and prove nothing.
        assert(has(smt, "(_ extract 8 8)"));
        assert(has(smt, "zero_extend"));
    }
    {
        // mull is the same shape: the high half is data, not a flag to drop.
        const Translation t = runFile("languages/cryptoline/instances/ok/mul_add.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "bvmul"));
        assert(has(smt, "(_ extract 15 8)"));   // the high half of an 8x8 product
        assert(has(smt, "(_ extract 7 0)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Carry, carry-in, borrow and joined multiplication are distinct
        // relations. In particular, subc/subs expose NOT-borrow while subb
        // exposes borrow.
        const Translation t = run(
            "proc flags(uint4 x, uint4 y, bit k) =\n{ true && true }\n"
            "subc c s x y; subb b d x y; adcs o a x y k;\n"
            "sbcs nc ns x y k; sbbs nb nd x y k;\n"
            "muls ov m x y; mulj wide x y;\n"
            "{ false && false }\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun wide () (_ BitVec 8)"));
        assert(has(smt, "declare-fun c () (_ BitVec 1)"));
        assert(has(smt, "declare-fun b () (_ BitVec 1)"));
        assert(has(smt, "bvnot y"));              // subc/sbcs carry encoding
        assert(has(smt, "bvsub"));                // subb/sbbs borrow encoding
        assert(has(smt, "bvmul"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // `nondet` is a fresh, unconstrained SSA value; cmov and comparisons
        // define their destinations exactly, with wide set results using all
        // ones rather than the integer value one.
        const Translation t = run(
            "proc nd(uint8 x, uint8 y, bit k) =\n{ true && true }\n"
            "nondet r@uint8; cmov q k x y; seteq e@uint8 x y; setne n x y;\n"
            "{ false && false }\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun r () (_ BitVec 8)"));
        assert(!has(smt, "(= r"));
        assert(has(smt, "#b11111111"));
        assert(has(smt, "ite"));
    }
    {
        // Unsuffixed add/sub/mul and the non-output shift forms carry separate
        // source safety obligations. `adds` and other output forms do not:
        // their overflow information is data rather than a rejected execution.
        const Translation add = run(
            "proc safe(uint4 x, uint4 y) =\n{ true && true }\n"
            "add z x y;\n{ true && true }\n");
        const Translation adds = run(
            "proc wrapped(uint4 x, uint4 y) =\n{ true && true }\n"
            "adds c z x y;\n{ true && true }\n");
        assert(add.ok() && adds.ok());
        assert(has(add.toSmt2(), "zero_extend 4"));
        assert(has(add.toSmt2(), "(not (= "));
        assert(!has(adds.toSmt2(), "(not (= "));
    }

    // ---- Obligation: split ASSERTS the identity relating parts to whole. ----
    {
        const Translation t = runFile("languages/cryptoline/instances/ok/split.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // `split` extends both pieces back to the source width. Narrow pieces
        // are produced by the distinct `spl` instruction.
        assert(has(smt, "declare-fun hi () (_ BitVec 8)"));
        assert(has(smt, "declare-fun lo () (_ BitVec 8)"));
        // Both halves are tied to x. Without these two equalities they are free
        // variables and `hi * 2**4 + lo = 0` says nothing about x at all.
        assert(has(smt, "(_ extract 7 4)"));
        assert(has(smt, "(_ extract 3 0)"));
        assert(has(smt, "zero_extend"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // `spl` is the narrow counterpart of `split`, and join reconstructs
        // the original width through SMT concat.
        const Translation t = run(
            "proc pieces(uint8 x) =\n{ true && true }\n"
            "spl h l x 3; join y h l;\n{ false && false }\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun h () (_ BitVec 5)"));
        assert(has(smt, "declare-fun l () (_ BitVec 3)"));
        assert(has(smt, "declare-fun y () (_ BitVec 8)"));
        assert(has(smt, "concat h l"));
    }

    // ---- Obligation: signedness picks the lift, and nothing else does. -----
    {
        const Translation t = runFile("languages/cryptoline/instances/ok/signedness.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // One file, one uint8 and one sint8, both lifted in the same
        // expression -- so neither conversion can be a global default, and a
        // frontend that picked one for everything fails whichever it picked.
        assert(has(smt, "bv2nat"));
        assert(has(smt, "sbv_to_int"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // And the choice follows the DECLARATION, not the position: swapping
        // the two declarations swaps the two conversions.
        const char* body =
            "\n{ true && true }\nmov v p;\nmov t q;\n{ eqn v = t && rng true }\n";
        const Translation a = run(std::string("proc s (uint8 p, sint8 q) =") + body);
        const Translation b = run(std::string("proc s (sint8 p, uint8 q) =") + body);
        assert(a.ok() && b.ok());
        assert(a.toSmt2() != b.toSmt2());
    }

    // ---- Obligation: straight-line SSA. ------------------------------------
    {
        const Translation t = runFile("languages/cryptoline/instances/ok/ssa.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // `x` is assigned twice, so there are two variables. Reusing one makes
        // `x = a` and `x = b` contradictory: the query goes unsat for a reason
        // that has nothing to do with the property, and reports "verified".
        assert(has(smt, "declare-fun x () (_ BitVec 8)"));
        assert(has(smt, "declare-fun x!2 () (_ BitVec 8)"));
        assert(t.report().stats().num_vars == 4);   // a, b, x, x!2

        const auto& beta = t.semantics().stages()[0].projection;
        bool final_x = false, leaked_version = false;
        for (const Sem::Observable& observable : beta.observables) {
            if (observable.source_name == "x" && observable.target_name == "x!2") {
                final_x = true;
            }
            if (observable.source_name == "x!2") { leaked_version = true; }
        }
        assert(final_x && !leaked_version);
        Sem::Assignment target{{"a", "#x01"}, {"b", "#x02"},
                               {"x", "#x01"}, {"x!2", "#x02"}};
        Sem::Assignment source;
        Diagnostics projection_diags;
        assert(t.semantics().project(target, source, projection_diags));
        assert(source.at("x") == "#x02");
        assert(source.find("x!2") == source.end());
    }

    // ---- Obligation: assume is a hypothesis, assert is an obligation. ------
    {
        const Translation t = runFile("languages/cryptoline/instances/ok/assume.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The assumed bound appears positively and the asserted one negated:
        // the script is a refutation, so UNSAT means the procedure is correct.
        // Assuming the obligation instead would make every procedure pass.
        assert(has(smt, "bvule") || has(smt, "bvuge"));
        assert(has(smt, "not"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The distinction, isolated: the same formula as an assume and as an
        // assert must not produce the same script.
        const char* head = "proc p (uint8 x) =\n{ true && true }\n";
        const Translation assumed =
            run(std::string(head) + "assume { rng x <= 4 }\n{ true && true }\n");
        const Translation asserted =
            run(std::string(head) + "assert { rng x <= 4 }\n{ true && true }\n");
        assert(assumed.ok() && asserted.ok());
        assert(assumed.toSmt2() != asserted.toSmt2());
    }
    {
        // Each assertion is checked at its own prefix. A later `assume false`
        // cannot erase a counterexample to an earlier assertion.
        const Translation t = run(
            "proc main (uint8 x) =\n"
            "{ true && true }\n"
            "assert { false && true }\n"
            "assume { false && true }\n"
            "{ true && true }\n");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 1);
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
        assert(t.semantics().stages()[0].decision.source
               == Sem::DecisionKind::PROGRAM_VERIFICATION);
        assert(!t.semantics().targetSatMeansSourceYes());
    }

    // ---- Exponentiation stays exact. ---------------------------------------
    {
        // `2**64` is routinely larger than 64 bits. Computed as decimal text,
        // because a long long would wrap -- and silently wrapping is the one
        // thing an overflow specification must not do.
        const Translation t = run(
            "proc big (uint8 x) =\n{ true && true }\nmov y x;\n"
            "{ eqn y = 2**64 && rng true }\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "18446744073709551616"));
    }

    // ---- Bitwise, shifts and cast. -----------------------------------------
    {
        const Translation t = runFile("languages/cryptoline/instances/ok/bitwise.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        for (const char* op : {"bvand", "bvor", "bvxor", "bvnot", "bvshl", "bvlshr"}) {
            assert(has(smt, op));
        }
        // cast to a wider unsigned type zero-extends; the direction and the
        // sign behaviour come from the declared types, never from the value.
        assert(has(smt, "zero_extend"));
        assert(has(smt, "declare-fun w () (_ BitVec 16)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A signed source sign-extends instead. Same instruction, different
        // declaration, different meaning -- and no line of the file says so.
        const Translation t = run(
            "proc cs (sint8 x) =\n{ true && true }\ncast sint16 w x;\n"
            "{ true && rng w = 0 }\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "sign_extend"));
    }
    {
        // vpc performs the same bit conversion as cast, but additionally asks
        // whether source and destination denote the same mathematical integer.
        // Widening uint8 -> uint16 is always safe; narrowing uint16 -> uint8
        // has counterexamples and therefore must not be treated as plain cast.
        const Translation safe =
            runFile("languages/cryptoline/instances/ok/vpc_safe.cl");
        const Translation unsafe =
            runFile("languages/cryptoline/instances/ok/vpc_counterexample.cl");
        assert(safe.ok() && unsafe.ok());
        assert(has(safe.toSmt2(), "zero_extend 8"));
        assert(has(safe.toSmt2(), "bv2nat"));
        assert(has(unsafe.toSmt2(), "(_ extract 7 0)"));
        assert(has(unsafe.toSmt2(), "(not (= "));
    }
    {
        // CryptoLine defines all range modular equalities in w+1 bits. Unsigned
        // equmod zero-extends, while the signed variants sign-extend; eqsrem is
        // deliberately remainder rather than modulo.
        const Translation t =
            runFile("languages/cryptoline/instances/ok/range_mod.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "zero_extend 1"));
        assert(has(smt, "sign_extend 1"));
        assert(has(smt, "bvsmod"));
        assert(has(smt, "bvsrem"));
        assert(has(smt, "#b000000000"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Typed constants and destination annotations are part of the source
        // type system, including historical @width syntax and hexadecimal
        // literals. Out-of-range constants are rejected rather than truncated.
        const Translation good = run(
            "proc lit(uint8 x) =\n{ true && true }\n"
            "mov a 0xff@uint8; cast b@sint16 x; mov c 3@8;\n"
            "{ false && false }\n");
        const Translation bad = run(
            "proc lit(uint8 x) =\n{ true && true }\n"
            "mov a 256@uint8;\n{ true && true }\n");
        assert(good.ok());
        assert(has(good.toSmt2(), "#b11111111"));
        assert(!bad.ok());
        assert(has(bad.diagnostics().all()[0].message, "outside uint8"));
    }

    // ---- Explicit signedness variants are typing contracts. -----------------
    {
        // u*/s* share the base instruction's graph; the prefix fixes the
        // interpretation and requires the operands to carry it already
        // (parsers/common.ml: parse_uadd_at hints typ_to_unsigned;
        // typecheck/std.ml: check_same_typ). One file exercises the whole
        // variant grid plus set/clear/nop.
        const Translation t =
            runFile("languages/cryptoline/instances/ok/signed_variants.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "bvadd"));
        assert(has(smt, "bvmul"));
        // smulj on two sint8 yields a signed double-width result...
        assert(has(smt, "declare-fun sj () (_ BitVec 16)"));
        // ...and the algebraic half lifts the unsigned a by bv2nat and the
        // signed b by bv2int -- the prefix, not a default, decided.
        assert(has(smt, "bv2nat"));
        assert(has(smt, "sbv_to_int"));
        // set/clear define their destinations as the bit constants 1/0.
        assert(has(smt, "declare-fun flag () (_ BitVec 1)"));
        assert(has(smt, "declare-fun done () (_ BitVec 1)"));
        // `/\` is the infix predicate conjunction.
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The prefix is a typing contract: uadd on signed operands and ssplit
        // on an unsigned source are ill-formed, not coerced.
        const Translation t =
            runFile("languages/cryptoline/instances/reject/uadd_signed.cl");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "unsigned variant"));
        const Translation s =
            runFile("languages/cryptoline/instances/reject/ssplit_unsigned.cl");
        assert(!s.ok());
        assert(s.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(s.diagnostics().all()[0].message, "signed variant"));
        const Translation w =
            runFile("languages/cryptoline/instances/reject/set_width.cl");
        assert(!w.ok());
        assert(w.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(w.diagnostics().all()[0].message, "bit"));
    }
    {
        // The signed types also spell `intN` (parsers/cryptolineLexer.mll).
        const Translation t = run(
            "proc p (int8 x) =\n{ true && true }\nmov y x;\n"
            "{ eqn y = x && rng true }\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "sbv_to_int"));
    }

    // ---- Range division is a direct SMT-LIB mapping, total at zero. --------
    {
        const Translation t =
            runFile("languages/cryptoline/instances/ok/range_division.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "bvudiv"));
        assert(has(smt, "bvsdiv"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
        // §4.5: the mapping needs no convention decision, but the reliance on
        // SMT-LIB's total-at-zero behaviour is RECORDED.
        bool udiv_recorded = false, sdiv_recorded = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.unified_op == "bvudiv") {
                udiv_recorded = true;
                assert(c.fidelity.sound && c.fidelity.complete && c.fidelity.preserves_optimum && c.fidelity.bounds.empty() && c.fidelity.count_status == CountStatus::UNASSESSED);
                assert(has(c.rationale, "total") || has(c.rationale, "TOTAL"));
            }
            if (c.unified_op == "bvsdiv") { sdiv_recorded = true; }
        }
        assert(udiv_recorded && sdiv_recorded);
    }

    // ---- The predicate-expression catalogue tail. ---------------------------
    {
        const Translation t =
            runFile("languages/cryptoline/instances/ok/predicate_catalogue.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Disjunction and negation in the range half...
        assert(has(smt, "(or "));
        assert(has(smt, "(not "));
        // ...the eqmod modulus list gets one existential multiplier each...
        assert(has(smt, "exists"));
        // ...the modular equality suffixes land in w+1 bits (smod of the
        // zero-extended difference, as for equmod)...
        assert(has(smt, "bvsmod"));
        // ...the infix arithmetic shift and the prefix forms...
        assert(has(smt, "bvashr"));
        // ...and expression exponentiation is a multiplication chain over Int.
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
        const Translation bad =
            runFile("languages/cryptoline/instances/reject/or_algebraic.cl");
        assert(!bad.ok());
        assert(bad.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(bad.diagnostics().all()[0].message, "conjunction-only"));
    }

    // ---- Cut fragments, chained. --------------------------------------------
    {
        // `cut` splits the verification into fragments, each refuted under
        // ONLY the previous cut's predicates (the official "starts afresh").
        // In cut_chain.cl the final fragment's obligations hold only THROUGH
        // the cut predicate: the fragment prefix no longer contains the
        // instruction that defined y. The chaining is therefore visible in
        // the text: the cut predicate appears positively (as the later
        // fragments' assumption) as well as negated (as fragment 0's
        // obligation). The verdicts are pinned by the Python verdict tests.
        const Translation t =
            runFile("languages/cryptoline/instances/ok/cut_chain.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        const std::string cut_predicate = "(bvule y #b00000101)";
        std::size_t occurrences = 0;
        for (std::size_t at = 0;
             (at = smt.find(cut_predicate, at)) != std::string::npos; ++at) {
            ++occurrences;
        }
        assert(occurrences >= 3);   // fragment 0 negates it; fragments 1 assume it
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
        // The fragment structure is RECORDED: one query is a disjunction of
        // per-fragment refutation branches.
        bool recorded = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.unified_op == "fragmented-refutation") {
                recorded = true;
                assert(c.fidelity.sound && c.fidelity.complete && c.fidelity.preserves_optimum && c.fidelity.bounds.empty() && c.fidelity.count_status == CountStatus::UNASSESSED);
                assert(has(c.rationale, "2 verification fragments"));
            }
        }
        assert(recorded);
    }
    {
        // check_index (the VMT/MoXI selector idiom) restricts the query to one
        // fragment; out-of-range is a parse error naming the fragment count.
        const Translation all =
            runFile("languages/cryptoline/instances/ok/cut_chain.cl");
        const Translation frag1 =
            runFile("languages/cryptoline/instances/ok/cut_chain.cl", "1");
        assert(all.ok() && frag1.ok());
        assert(all.toSmt2() != frag1.toSmt2());
        ParserPtr reader = newParser();
        assert(reader->parseStr(frag1.toSmt2()));
        const Translation oob =
            runFile("languages/cryptoline/instances/ok/cut_chain.cl", "5");
        assert(!oob.ok());
        assert(oob.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(oob.diagnostics().all()[0].message, "2 fragments"));
    }
    {
        // The fixture that pinned the old refusal now translates -- its cut
        // predicate does not follow from the prefix, so the instance HAS a
        // counterexample (the verdict is pinned in Python with z3).
        const Translation t = runFile("languages/cryptoline/instances/ok/cut.cl");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
        // ecut/rcut cut one side only; cut_broken.cl's ecut predicate y = x+1
        // never holds, so its fragment branch is satisfiable as text: the
        // algebraic cut obligation appears negated there (the lowering prints
        // (not (= a b)) as (distinct a b)).
        const Translation b =
            runFile("languages/cryptoline/instances/ok/cut_broken.cl");
        assert(b.ok());
        assert(has(b.toSmt2(), "(distinct (+ 1 (bv2nat x)) (bv2nat y))"));
        assert(reader->parseStr(b.toSmt2()));
    }
    {
        // Prove-with fact selection: the final fragment's chain knows only
        // z <=u 6; the postcondition's other conjunct is cut 0's predicate,
        // selected by `prove with [ cuts [0] ]`. The text shows the selected
        // fact joins the final branch.
        const Translation t =
            runFile("languages/cryptoline/instances/ok/cut_prove_with.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(bvule y #b00000101)"));
        assert(has(smt, "(bvule z #b00000110)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
        const Translation oob =
            runFile("languages/cryptoline/instances/reject/cut_index_oob.cl");
        assert(!oob.ok());
        assert(oob.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(oob.diagnostics().all()[0].message, "cuts precede"));
    }
    {
        // eassert/rassert assert one side only.
        const Translation t =
            runFile("languages/cryptoline/instances/ok/eassert_rassert.cl");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }

    // ---- Procedures: call is the contract, inline is the body. -------------
    {
        // `call` is replaced by the callee's pre-/post-conditions
        // (parsers/common.ml: parse_call_at): the precondition is ASSERTED
        // (an obligation, negated), the outputs are havocked, the
        // postcondition is ASSUMED (appears positively, unconsumed).
        const Translation t = runFile("languages/cryptoline/instances/ok/call.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(not (bvule x #b01100100))"));   // the caller must prove a<=100
        assert(has(smt, "declare-fun y () (_ BitVec 8)"));
        assert(has(smt, "(bvule y #b11001000)"));          // the assumed post
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // An actual used as input AND output has its entry value captured by
        // a fresh ghost, so the assumed postcondition relates the output to
        // the call-time input (parse_call_at: mk_ghost_instr_for_actuals).
        const Translation t =
            runFile("languages/cryptoline/instances/ok/call_inout.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun callghost!"));
        // x is defined twice: the entry version (equated with the ghost) and
        // the havocked output version.
        assert(has(smt, "declare-fun x!2 () (_ BitVec 8)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // `inline` splices the BODY: the callee's instruction equations reach
        // the caller's obligations (here the addition that defines y).
        const Translation t = runFile("languages/cryptoline/instances/ok/inline.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "bvadd"));
        assert(has(smt, "(bvule y #b11001000)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
        // inlinespec verifies through the contract like call.
        const Translation s =
            runFile("languages/cryptoline/instances/ok/inlinespec.cl");
        assert(s.ok());
        assert(reader->parseStr(s.toSmt2()));
    }
    {
        // The procedure-level checks are the official ones: a callee must be
        // declared EARLIER and not be main; counts and types match; output
        // actuals are distinct variables.
        const Translation self = run(
            "proc main(uint8 x) =\n{ true && true }\ncall main(x);\n"
            "{ true && rng true }\n");
        assert(!self.ok());
        assert(has(self.diagnostics().all()[0].message, "main"));
        const Translation dup = run(
            "proc p(uint8 a; uint8 r, uint8 s) =\n"
            "{ true && true }\nmov r a;\nmov s a;\n{ true && rng true }\n"
            "proc main(uint8 x) =\n{ true && true }\ncall p(x, y, y);\n"
            "{ true && rng true }\n");
        assert(!dup.ok());
        assert(has(dup.diagnostics().all()[0].message, "distinct"));
        const Translation count = run(
            "proc p(uint8 a; uint8 r) =\n{ true && true }\nmov r a;\n"
            "{ true && rng true }\n"
            "proc main(uint8 x) =\n{ true && true }\ncall p(x);\n"
            "{ true && rng true }\n");
        assert(!count.ok());
        assert(has(count.diagnostics().all()[0].message, "number of actual"));
    }
    {
        // Ghost variables are specification-only constants whose predicate is
        // always assumed (doc/cryptoline.pdf): ghost.cl captures x's value in
        // x0 before x is overwritten. The verdicts are pinned in Python.
        const Translation t = runFile("languages/cryptoline/instances/ok/ghost.cl");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun x0 () (_ BitVec 8)"));
        assert(has(smt, "(= x x0)") || has(smt, "(= x0 x)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The ghost declaration checks are the official ones
        // (typecheck/std.ml: ghost_disjoint; parsers/common.ml:
        // parse_ghost_at), and a ghost is never an instruction operand.
        const Translation operand =
            runFile("languages/cryptoline/instances/reject/ghost_operand.cl");
        assert(!operand.ok());
        assert(operand.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(operand.diagnostics().all()[0].message, "ghost variable"));
        const Translation mention =
            runFile("languages/cryptoline/instances/reject/ghost_no_mention.cl");
        assert(!mention.ok());
        assert(has(mention.diagnostics().all()[0].message, "without using any of the ghost"));
        const Translation collide =
            runFile("languages/cryptoline/instances/reject/ghost_redefines.cl");
        assert(!collide.ok());
        assert(has(collide.diagnostics().all()[0].message, "collides with a program variable"));
    }
    {
        // Named refusals: vectors and named constants are implementation
        // extensions / statement forms outside the manual's scalar grammar.
        const Translation vec =
            runFile("languages/cryptoline/instances/reject/vector.cl");
        assert(!vec.ok());
        assert(vec.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(vec.diagnostics().all()[0].message, "vector"));
        const Translation konst =
            runFile("languages/cryptoline/instances/reject/const_decl.cl");
        assert(!konst.ok());
        assert(konst.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(konst.diagnostics().all()[0].message, "named integer constants"));
        const Translation nocallee =
            runFile("languages/cryptoline/instances/reject/call_undefined.cl");
        assert(!nocallee.ok());
        assert(has(nocallee.diagnostics().all()[0].message, "undefined procedure"));
        const Translation nomain =
            runFile("languages/cryptoline/instances/reject/no_main.cl");
        assert(!nomain.ok());
        assert(has(nomain.diagnostics().all()[0].message, "no 'main' procedure"));
    }

    // ---- Refusals. ----------------------------------------------------------
    {
        const Translation t =
            runFile("languages/cryptoline/instances/reject/unknown_instruction.cl");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "foobar"));
        // The message says what skipping would cost, so the refusal is not
        // mistaken for pedantry.
        assert(has(t.diagnostics().all()[0].message, "vacuous"));
    }
    {
        // No implicit widening: an 8-bit and a 16-bit operand is a type error,
        // not a silently zero-extended addition in a different arithmetic.
        const Translation t =
            runFile("languages/cryptoline/instances/reject/width_mismatch.cl");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(t.diagnostics().all()[0].message, "implicit conversion"));
    }
    {
        const Translation t = runFile("languages/cryptoline/instances/reject/undefined.cl");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "before it is defined"));
    }
    {
        const Translation t = runFile("languages/cryptoline/instances/reject/bad_type.cl");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }
    {
        const Translation t = runFile("languages/cryptoline/instances/nosuch.cl");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }
    {
        // A file with no postcondition is malformed, not a procedure with a
        // vacuous one -- which would "verify" every program.
        const Translation t = run("proc p (uint8 x) =\n{ true && true }\nmov y x;\n");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "postcondition"));
    }

    // ---- The signedness lift is RECORDED. ----------------------------------
    //
    // This file's own document calls it "the first frontend whose correctness
    // turns on the bv2nat / bv2int choice": the algebraic half of a condition is
    // integer arithmetic over bit-vector VALUES, and the declared signedness is
    // the only evidence for which reading is meant. Both operators are
    // BitVec -> Int, so the emitted script does not say which was taken, and the
    // wrong one shifts every negative value by exactly 2^w while type-checking
    // perfectly.
    //
    // That is precisely what an EncodingChoice is for -- a decision no later
    // stage can see being made -- and it was not recorded at all. An audit of
    // every frontend for unrecorded decisions is what found it.
    {
        const Translation t = run(
            "proc main(uint64 x, sint64 y) =\n{ true && true }\n"
            "mov a x;\nmov b y;\n{ eqn a = x && true }\n");
        assert(t.ok());
        bool unsigned_lift = false, signed_lift = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.unified_op == "bv2nat") { unsigned_lift = true; }
            if (c.unified_op == "bv2int") { signed_lift = true; }
            // Exact: the declaration determines the reading, so nothing is
            // approximated -- what is recorded is WHICH reading, not a loss.
            if (c.unified_op == "bv2nat" || c.unified_op == "bv2int") {
                assert(c.fidelity.sound && c.fidelity.complete && c.fidelity.preserves_optimum && c.fidelity.bounds.empty() && c.fidelity.count_status == CountStatus::UNASSESSED);
            }
        }
        // `x` is uintN, so its lift is bv2nat. The signed one appears only when a
        // sintN variable reaches the algebraic half.
        assert(unsigned_lift);
        (void)signed_lift;
    }

    std::cout << "All CryptoLine tests passed." << std::endl;
    return 0;
}
