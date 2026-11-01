// A group of mutually recursive datatypes is one command, and was two.
//
// SMT-LIB declares a whole group in a single `declare-datatypes` precisely so
// that its members may refer to each other: the sort names are all in scope
// before any constructor list is read. `dumpSMT2` emitted one command per SORT,
// which is right for a datatype that stands alone and impossible for a pair
// that does not:
//
//     (declare-datatypes ((T 0)) (((node (kids TL)) ...)))   <- TL not declared
//     (declare-datatypes ((TL 0)) (((tcons (thd T) ...))))
//
// Re-parsing that failed with `Unknown or unexpected symbol "TL"`. The dump
// returned the text and reported nothing, so a script this parser had read
// perfectly came back out unreadable -- by itself, and by anything else.
//
// The fix groups by strongly connected component and emits the groups in
// dependency order. A datatype that depends on nothing keeps its own command,
// so the output of every non-mutual script is byte-for-byte what it was.

#include "somtparser/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0;
    for (std::size_t i = hay.find(needle); i != std::string::npos;
         i = hay.find(needle, i + 1)) {
        ++n;
    }
    return n;
}

/** Parse, dump, and require the dump to read back -- which is the property
 *  this file is about, so it is checked on every case rather than once. */
std::string roundTrip(const std::string& script, const char* what) {
    ParserPtr p = newParser();
    if (!p->parseStr(script)) {
        std::cout << "  failed to parse (" << what << "):\n" << script;
        VERIFY(false);
    }
    const std::string out = p->dumpSMT2();
    ParserPtr q = newParser();
    if (!q->parseStr(out)) {
        std::cout << "  dump does not read back (" << what << "):\n" << out;
        VERIFY(false);
    }
    // And is stable: a second dump equals the first, so the grouping does not
    // drift on each pass.
    VERIFY(q->dumpSMT2() == out);
    return out;
}

} // namespace

int main() {
    std::cout << "======= datatype declaration groups =======\n";

    // ---- Mutually recursive: ONE command. ----------------------------------
    {
        const std::string out = roundTrip(
            "(set-logic ALL)\n"
            "(declare-datatypes ((T 0) (TL 0))"
            " (((node (kids TL)) (leaf (val Int))) ((tnil) (tcons (thd T) (ttl TL)))))\n"
            "(declare-const t T)\n(assert ((_ is leaf) t))\n(check-sat)\n",
            "mutual recursion");
        VERIFY(count(out, "(declare-datatypes") == 1);
        VERIFY(has(out, "(T 0) (TL 0)"));
    }
    {
        // Three in a cycle, to check the grouping is not a two-element special
        // case dressed up as a general one.
        const std::string out = roundTrip(
            "(set-logic ALL)\n"
            "(declare-datatypes ((A 0) (B 0) (C 0))"
            " (((mkA (toB B))) ((mkB (toC C))) ((mkC (toA A)) (stop))))\n"
            "(declare-const a A)\n(assert ((_ is mkA) a))\n(check-sat)\n",
            "three-cycle");
        VERIFY(count(out, "(declare-datatypes") == 1);
    }

    {
        const std::string out = roundTrip(
            "(set-logic ALL)"
            "(declare-codatatypes ((S 0) (T 0)) (((A (a T))) ((B (b S)))))"
            "(declare-const s S)(assert (= s (A (B s))))(check-sat)",
            "mutually corecursive types");
        VERIFY(count(out, "(declare-codatatypes") == 1);
        VERIFY(count(out, "(declare-datatypes") == 0);
    }
    {
        const std::string out = roundTrip(
            "(set-logic ALL)"
            "(declare-codatatypes ((S 1)) ((par (X) ((cons (hd X) (tl (S X)))))))"
            "(declare-const s (S Int))(assert (= s (cons 4 s)))(check-sat)",
            "parametric corecursive type");
        VERIFY(count(out, "(declare-codatatypes") == 1);
        VERIFY(has(out, "(par (X)"));
    }

    // ---- Standing alone: unchanged, one command each. -----------------------
    {
        // The case every existing script and every corpus file is, so its
        // output must be exactly what it was before the grouping existed.
        const std::string out = roundTrip(
            "(set-logic ALL)\n"
            "(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n"
            "(declare-const l Lst)\n(assert ((_ is cons) l))\n(check-sat)\n",
            "self-recursive");
        VERIFY(count(out, "(declare-datatypes") == 1);
        VERIFY(has(out,
                   "(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))"));
    }
    {
        // Two that do not refer to each other stay two commands. Merging them
        // would be legal SMT-LIB and would still change the shape of a script
        // that had nothing wrong with it.
        const std::string out = roundTrip(
            "(set-logic ALL)\n"
            "(declare-datatypes ((A 0)) (((a1) (a2))))\n"
            "(declare-datatypes ((B 0)) (((b1) (b2))))\n"
            "(declare-const x A)\n(declare-const y B)\n"
            "(assert ((_ is a1) x))\n(check-sat)\n",
            "two independent");
        VERIFY(count(out, "(declare-datatypes") == 2);
    }

    // ---- One-way dependency: the dependency comes FIRST. --------------------
    {
        // Not mutual, so two commands -- but the order is forced, and it is not
        // the declaration order in general. Here it happens to agree; the next
        // case is the one where it does not.
        const std::string out = roundTrip(
            "(set-logic ALL)\n"
            "(declare-datatypes ((B 0)) (((b1) (b2))))\n"
            "(declare-datatypes ((A 0)) (((wrap (unwrap B)))))\n"
            "(declare-const x A)\n(assert ((_ is wrap) x))\n(check-sat)\n",
            "dependency in declaration order");
        VERIFY(count(out, "(declare-datatypes") == 2);
        VERIFY(out.find("(B 0)") < out.find("(A 0)"));
    }
    {
        // The same two declared in ONE command, where the group lists A before
        // the B it needs. Split into two, they must come out B first -- the
        // order the reader needs, not the order the writer used.
        const std::string out = roundTrip(
            "(set-logic ALL)\n"
            "(declare-datatypes ((A 0) (B 0)) (((wrap (unwrap B))) ((b1) (b2))))\n"
            "(declare-const x A)\n(assert ((_ is wrap) x))\n(check-sat)\n",
            "dependency against declaration order");
        VERIFY(out.find("(B 0)") < out.find("(A 0)"));
    }

    // ---- The members are still not declared twice. -------------------------
    {
        // A datatype declaration registers a function for every constructor,
        // selector and tester. Emitting those as declare-funs beside the
        // datatype makes the script refuse itself as a redeclaration, and the
        // grouping rewrite moved the code that collects their names.
        const std::string out = roundTrip(
            "(set-logic ALL)\n"
            "(declare-datatypes ((T 0) (TL 0))"
            " (((node (kids TL)) (leaf (val Int))) ((tnil) (tcons (thd T) (ttl TL)))))\n"
            "(declare-const t T)\n(assert ((_ is leaf) t))\n(check-sat)\n",
            "no duplicate members");
        VERIFY(!has(out, "(declare-fun node"));
        VERIFY(!has(out, "(declare-fun val"));
        VERIFY(!has(out, "(declare-fun is-leaf"));
    }

    // ---- The dependency may be NESTED inside a sort. -----------------------
    //
    // A selector of sort `(Array Int TL)` depends on TL exactly as one of sort
    // `TL` does. The scan read only the OUTERMOST sort name, so it missed the
    // edge: the two datatypes landed in different groups, were emitted as
    // separate commands, and the second was named before it was declared --
    // this file's own defect, reached through a sort constructor.
    //
    // Worth naming as a class rather than as a case. The first round of this
    // fix tested `T` mentioning `TL` DIRECTLY, which is the shape a test author
    // reaches for; `(Array Int TL)` and `(Set Q)` are the shapes a real model
    // uses, because a datatype usually refers to a COLLECTION of another one.
    {
        const std::string out = roundTrip(
            "(declare-datatypes ((T 0) (TL 0))"
            " (((node (kids (Array Int TL))) (leaf))"
            "  ((tnil) (tcons (thd T)))))\n",
            "mutual recursion through an array");
        VERIFY(count(out, "(declare-datatypes") == 1);
    }
    {
        const std::string out = roundTrip(
            "(declare-datatypes ((P 0) (Q 0))"
            " (((p1 (pq (Set Q))) (p2))"
            "  ((q1 (qp P)))))\n",
            "mutual recursion through a set");
        VERIFY(count(out, "(declare-datatypes") == 1);
    }
    {
        // Two levels down, which a scan looking one level deep would still miss.
        const std::string out = roundTrip(
            "(declare-datatypes ((U 0) (V 0))"
            " (((u1 (uv (Array Int (Array Int V)))) (u2))"
            "  ((v1 (vu U)))))\n",
            "mutual recursion two sorts deep");
        VERIFY(count(out, "(declare-datatypes") == 1);
    }
    {
        // A ONE-WAY nested dependency still gets two commands, in the order
        // that declares the dependency first: grouping is for cycles, and
        // merging independent datatypes would change correct output.
        const std::string out = roundTrip(
            "(declare-datatypes ((W 0) (Z 0))"
            " (((w1 (wz (Array Int Z))))"
            "  ((z1) (z2))))\n",
            "one-way dependency through an array");
        VERIFY(count(out, "(declare-datatypes") == 2);
        VERIFY(out.find("(Z 0)") < out.find("(W 0)"));
    }

    // ---- Parametric datatypes: SMT-LIB's `par` form. -----------------------
    //
    // `(declare-datatypes ((L 1)) ((par (X) (...))))` did not parse at all --
    // the arity was read and the body then had no syntax for the parameter it
    // announced, so a form the standard defines failed with `"(" missing`, a
    // tokeniser complaint. The parameters are sorts, and inside the body they
    // are ordinary sorts in scope; outside it they must be gone, or the next
    // command would see a sort the script never declared.
    {
        const std::string out = roundTrip(
            "(declare-datatypes ((L 1))"
            " ((par (X) ((nil) (cons (hd X) (tl (L X)))))))\n",
            "parametric list");
        // The `par` form is written back, and with the parameter's own NAME:
        // a Sort records its arity, not what its parameters were called, so
        // this only works because the names are carried from the declaration.
        VERIFY(has(out, "par (X)"));
        VERIFY(has(out, "(L 1)"));
        VERIFY(has(out, "(hd X)"));
        VERIFY(has(out, "(tl (L X))"));
    }
    {
        // Two parameters, and the singular `declare-datatype` spelling, where
        // the arity is not written down -- it is however many `par` binds.
        const std::string out = roundTrip(
            "(declare-datatype Pair (par (A B) ((mk (fst A) (snd B)))))\n",
            "parametric pair, singular form");
        VERIFY(has(out, "par (A B)"));
        VERIFY(has(out, "(Pair 2)"));
    }
    {
        // A parameter is bound by its `par` and is not in scope afterwards. If
        // it leaked, this would declare a variable of a sort the script never
        // declared and the dump would not read back.
        ParserPtr p = newParser();
        VERIFY(p->parseStr("(declare-datatypes ((L 1))"
                           " ((par (X) ((nil) (cons (hd X) (tl (L X)))))))\n"));
        VERIFY(!p->parseStr("(declare-fun leaked () X)\n"));
    }
    {
        // Mutual recursion BETWEEN parametric datatypes: one group, one
        // command, each with its own parameter name.
        const std::string out = roundTrip(
            "(declare-datatypes ((T 1) (TL 1))"
            " ((par (X) ((node (kids (TL X))) (leaf (val X))))"
            "  (par (Y) ((tnil) (tcons (thd (T Y)) (ttl (TL Y)))))))\n",
            "mutually recursive parametric datatypes");
        VERIFY(count(out, "(declare-datatypes") == 1);
        VERIFY(has(out, "par (X)"));
        VERIFY(has(out, "par (Y)"));
    }
    {
        // A NON-parametric datatype keeps its plain body: `par` is not written
        // for an arity-0 datatype, so every existing script's output is
        // unchanged.
        const std::string out = roundTrip(
            "(declare-datatypes ((C 0)) (((r) (g) (b))))\n", "no par when arity 0");
        VERIFY(!has(out, "par"));
    }

    // ---- Applying a parametric datatype's members. --------------------------
    //
    // A member of a parametric datatype is POLYMORPHIC, and its declaration
    // records the parameters rather than an instance: `hd` is declared
    // `L -> X`. Applying it to an `(L Int)` has to give `Int`, and without the
    // substitution it gave `X` -- a sort no longer in scope, so the next
    // operator over the term reported a type mismatch naming a symbol the
    // script never wrote.
    {
        ParserPtr p = newParser();
        VERIFY(p->parseStr(
            "(declare-datatypes ((L 1))"
            " ((par (X) ((nil) (cons (hd X) (tl (L X)))))))\n"
            "(declare-fun l () (L Int))\n"
            "(assert (> (hd l) 0))\n"));
        const std::string out = p->dumpSMT2();
        // The instantiated sort survives to the declaration, so a reader knows
        // WHICH instance the variable is of.
        VERIFY(has(out, "(declare-fun l () (L Int))"));
        ParserPtr q = newParser();
        VERIFY(q->parseStr(out));
    }
    {
        // ...and the substitution must not accept the wrong instance: `hd` of
        // an `(L Int)` is an Int, so comparing it to a Bool is a type error and
        // has to stay one. A substitution that returned the parameter unchanged
        // would make both this and the case above fail; one that returned
        // anything would make both pass.
        ParserPtr p = newParser();
        VERIFY(!p->parseStr(
            "(declare-datatypes ((L 1))"
            " ((par (X) ((nil) (cons (hd X) (tl (L X)))))))\n"
            "(declare-fun l () (L Int))\n"
            "(assert (= (hd l) true))\n"));
    }
    {
        // A selector whose result is the datatype itself: `tl` of an `(L Int)`
        // is an `(L Int)`, not a bare `L`, so it can be selected from again.
        ParserPtr p = newParser();
        VERIFY(p->parseStr(
            "(declare-datatypes ((L 1))"
            " ((par (X) ((nil) (cons (hd X) (tl (L X)))))))\n"
            "(declare-fun l () (L Int))\n"
            "(assert (> (hd (tl l)) 0))\n"));
        ParserPtr q = newParser();
        VERIFY(q->parseStr(p->dumpSMT2()));
    }

    {
        // `(as nil (L Int))` -- ASCRIBING which instance a constructor builds.
        // `nil` mentions none of the parameters, so it has no arguments to
        // infer them from and SMT-LIB makes the script say. Without it a
        // parametric datatype has declarations and no way to build a value.
        ParserPtr p = newParser();
        VERIFY(p->parseStr(
            "(declare-datatypes ((L 1))"
            " ((par (X) ((nil) (cons (hd X) (tl (L X)))))))\n"
            "(declare-fun l () (L Int))\n"
            "(assert (= l (cons 1 (as nil (L Int)))))\n"));
        const std::string out = p->dumpSMT2();
        ParserPtr q = newParser();
        VERIFY(q->parseStr(out));
        VERIFY(q->dumpSMT2() == out);
    }
    {
        // The ascription is what decides the instance, so a constructor built
        // at the wrong one must not be accepted: `(as nil (L Bool))` is not an
        // `(L Int)` and the equality is a type error.
        ParserPtr p = newParser();
        VERIFY(!p->parseStr(
            "(declare-datatypes ((L 1))"
            " ((par (X) ((nil) (cons (hd X) (tl (L X)))))))\n"
            "(declare-fun l () (L Int))\n"
            "(assert (= l (as nil (L Bool))))\n"));
    }

    std::cout << "All datatype-group tests passed." << std::endl;
    return 0;
}
