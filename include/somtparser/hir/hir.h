/* -*- Header -*-
 *
 * HIR — the one intermediate representation.
 *
 * There is no separate low-level IR. "Low level" is an invariant on this same
 * structure: every high-level Feature has been eliminated by the pass pipeline.
 * A second IR would be a third representation of what DAGNode already is.
 *
 * Expressions are immutable and shared; the ConstraintModel container is
 * mutable. Passes rebuild expressions and edit the ConstraintModel in place,
 * mirroring how the existing Rewriter rebuilds through NodeManager, and
 * letting Python hold references safely.
 *
 * This task defines the minimum needed for the walking skeleton. Sets,
 * comprehensions, arrays, transition systems and Horn clauses arrive with the
 * languages that need them.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_HIR_HIR_HEADER
#define SOMTPARSER_HIR_HIR_HEADER

#include "somtparser/translation/diagnostic.h"
#include "somtparser/hir/feature.h"

#include <atomic>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SOMTParser::Uir::Hir {

enum class SortKind {
    BOOL, INT, REAL,
    ARRAY,          // (Array index elem) -- a *total* function; see below
    BITVEC,         // (_ BitVec width)
    FLOAT,          // (_ FloatingPoint eb sb)
    STRING,
    UNINTERPRETED,  // declare-sort, arity 0
    /** SMT-LIB's RoundingMode.
     *
     *  A *sort*, not an attribute of the arithmetic operators, because that is
     *  what SMT-LIB says: it has five constants (RNE, RNA, RTP, RTN, RTZ) and a
     *  term of the sort may be a variable, so `fp.add rm x y` with a symbolic
     *  `rm` is a legal and useful thing to write -- it asks the solver which
     *  rounding mode makes the property fail. Putting the mode on the operator
     *  would make that unsayable. */
    ROUNDING_MODE,
    /** SMT-LIB's RegLan: the sort of regular expressions over strings.
     *
     *  A sort rather than a syntactic annotation on str.in_re, because that is
     *  what SMT-LIB says and because regular expressions compose -- re.union of
     *  two re.concats is an ordinary term, and a variable of the sort is
     *  legal. Most string benchmarks are mostly membership constraints, so a
     *  string theory without this carries the operators and not the corpus
     *  (docs/languages/smtlib2.md). */
    REGLAN,
    /** An algebraic datatype declared by the model, its name in Sort::name.
     *
     *  Like UNINTERPRETED, two datatype sorts are the same one exactly when
     *  their names match -- the constructors live in ConstraintModel::datatypes
     *  rather than in the sort, so that a sort stays a small value that can be
     *  copied and compared without carrying a whole declaration with it. */
    DATATYPE,
    /** `(Set T)` -- a finite set, its element sort in Sort::elem.
     *
     *  Reuses `elem` rather than adding a field: a set is a container of one
     *  sort, which is what `elem` already means for an array. `index` stays
     *  null, and sameSort compares only `elem`. */
    SET,
    /** `(Tuple T1 ... Tn)` -- a heterogeneous product, its FIELD sorts in
     *  Sort::args.
     *
     *  `args` rather than `elem`, because a tuple's fields are not one sort:
     *  `(Tuple Int Bool)` is the sort of a pair whose halves are checked
     *  separately, and folding them into a single element sort would make
     *  `(Tuple Int Bool)` and `(Tuple Bool Int)` indistinguishable. It reuses
     *  the field a parametric datatype already uses for the same reason -- a
     *  vector of sorts that makes a Sort recursive without making it large.
     *
     *  There is no `name`: unlike a datatype, two tuple sorts are the same one
     *  exactly when their fields match, position by position. That is why the
     *  lowering can CREATE the sort rather than resolve a declaration -- a
     *  tuple sort is never declared by a script, it is written down where it
     *  is used.
     *
     *  The NULLARY case is SMT-LIB's `UnitTuple`, an empty `args`. It is a
     *  real sort with exactly one value (`tuple.unit`) and not a malformed
     *  tuple, so nothing here may treat an empty field list as an error. */
    TUPLE,
};

/**
 * ARRAY is SMT-LIB's array and nothing else: a *total* function from the index
 * sort to the element sort.
 *
 * That totality is why there is one array type rather than three
 * (docs/hir-design-decisions-2026-08-12.md §3.1). A MiniZinc
 * `array[1..n] of var int` is this same object; the index set `1..n` is not part
 * of the sort but a statement about which indices are constrained, and it is
 * written as an ordinary constraint -- `forall i. 1 <= i <= n -> ...`. Designing
 * an index-set-aware array instead would have forced a compromise on cluster F,
 * which wants exactly SMT-LIB's.
 */
struct Sort {
    // Immutable sort DAGs can be as deep as expressions. Final release must
    // not recurse through index, element, or sort-constructor arguments.
    ~Sort() noexcept;

    SortKind kind = SortKind::BOOL;
    // Only for ARRAY. shared_ptr because a Sort is a value passed by value and
    // an array sort is recursive.
    std::shared_ptr<const Sort> index{};
    std::shared_ptr<const Sort> elem{};
    /** BITVEC. A width is part of the sort, not of each operation -- which is
     *  what both BTOR2 and SMT-LIB say, so putting it on operators instead
     *  would give every other sort a field that means nothing
     *  (docs/languages/btor2.md §4.1). Widths are arbitrary, not machine-sized:
     *  CryptoLine's specifications are statements about 256-bit values
     *  (docs/languages/cryptoline.md §4.6). */
    unsigned width = 0;
    /** FLOAT, as SMT-LIB's (_ FloatingPoint eb sb). */
    unsigned exponent_bits = 0;
    unsigned significand_bits = 0;
    /** UNINTERPRETED and DATATYPE. The sort's declared name. Two uninterpreted
     *  sorts are the same sort exactly when their names AND their arguments
     *  match -- see `args`. */
    std::string name{};
    /** UNINTERPRETED, when the name is a sort CONSTRUCTOR applied to arguments.
     *
     *  `(declare-sort S 1)` does not declare a sort; it declares a function
     *  from sorts to sorts, and `(S Bool)` and `(S Int)` are two of its values
     *  (SMT-LIB 2.6 §3.6). Empty for the ordinary arity-0 case, which is what
     *  `uninterpreted()` builds and what almost every frontend uses.
     *
     *  Kept as a vector of shared_ptr for the reason `index` and `elem` are: a
     *  Sort is a value passed by value, and this makes it recursive --
     *  `(S (S Int))` is legal. */
    std::vector<std::shared_ptr<const Sort>> args{};

    // Non-semantic scratch for allocation-free final release. A queued sort
    // owns one temporary self-reference; its other owners can still read the
    // immutable sort. Copies start with a fresh link, never with a copied pin.
    // Keep this last so existing aggregate initialization remains compatible.
    struct ReclamationLink {
        std::atomic_flag busy = ATOMIC_FLAG_INIT;
        const Sort* next = nullptr;
        std::shared_ptr<const Sort> owner;
        ReclamationLink() noexcept = default;
        ReclamationLink(const ReclamationLink&) noexcept {}
        ReclamationLink& operator=(const ReclamationLink&) noexcept { return *this; }
    };
    mutable ReclamationLink reclamation{};

    static Sort boolean() { return Sort{SortKind::BOOL, nullptr, nullptr}; }
    static Sort integer() { return Sort{SortKind::INT,  nullptr, nullptr}; }
    static Sort real()    { return Sort{SortKind::REAL, nullptr, nullptr}; }
    static Sort array(Sort index_sort, Sort elem_sort) {
        Sort s;
        s.kind = SortKind::ARRAY;
        s.index = std::make_shared<const Sort>(std::move(index_sort));
        s.elem  = std::make_shared<const Sort>(std::move(elem_sort));
        return s;
    }
    static Sort bitvec(unsigned w) {
        Sort s;
        s.kind = SortKind::BITVEC;
        s.width = w;
        return s;
    }
    static Sort floating(unsigned exponent, unsigned significand) {
        Sort s;
        s.kind = SortKind::FLOAT;
        s.exponent_bits = exponent;
        s.significand_bits = significand;
        return s;
    }
    static Sort string() { return Sort{SortKind::STRING}; }
    static Sort roundingMode() { return Sort{SortKind::ROUNDING_MODE}; }
    static Sort regLan() { return Sort{SortKind::REGLAN}; }
    static Sort set(Sort element) {
        Sort s;
        s.kind = SortKind::SET;
        s.elem = std::make_shared<const Sort>(std::move(element));
        return s;
    }
    static Sort datatype(std::string dt_name) {
        Sort s;
        s.kind = SortKind::DATATYPE;
        s.name = std::move(dt_name);
        return s;
    }
    /** A PARAMETRIC datatype applied to its arguments: `(L Int)`. Distinct from
     *  `(L Bool)` and from the unapplied `L`, which sameSort enforces. */
    static Sort datatype(std::string dt_name, std::vector<Sort> arguments) {
        Sort s;
        s.kind = SortKind::DATATYPE;
        s.name = std::move(dt_name);
        for (Sort& a : arguments) {
            s.args.push_back(std::make_shared<const Sort>(std::move(a)));
        }
        return s;
    }
    static Sort uninterpreted(std::string sort_name) {
        Sort s;
        s.kind = SortKind::UNINTERPRETED;
        s.name = std::move(sort_name);
        return s;
    }
    /** `(S Bool)` -- a sort constructor applied to arguments. @p arguments must
     *  be non-empty; the arity-0 case is `uninterpreted()`. The arity of the
     *  constructor is `arguments.size()`, so the declaration it needs is
     *  derivable and is not carried separately. */
    static Sort sortApp(std::string ctor_name, std::vector<Sort> arguments) {
        Sort s;
        s.kind = SortKind::UNINTERPRETED;
        s.name = std::move(ctor_name);
        s.args.reserve(arguments.size());
        for (Sort& a : arguments) {
            s.args.push_back(std::make_shared<const Sort>(std::move(a)));
        }
        return s;
    }
    /** `(Tuple T1 ... Tn)`, its fields in order. An EMPTY list is `UnitTuple`
     *  and is well formed -- see SortKind::TUPLE. */
    static Sort tuple(std::vector<Sort> fields) {
        Sort s;
        s.kind = SortKind::TUPLE;
        s.args.reserve(fields.size());
        for (Sort& f : fields) {
            s.args.push_back(std::make_shared<const Sort>(std::move(f)));
        }
        return s;
    }
};

/** Structural equality. Two array sorts are equal when their index and element
 *  sorts are, which is what a type check has to compare. */
bool sameSort(const Sort& a, const Sort& b);

/**
 * The sort in SMT-LIB spelling: `Int`, `(_ BitVec 8)`, `(Array Int Bool)`.
 *
 * Diagnostics must print this and not the bare kind. A message built from the
 * kind alone reads "'x' is used as BitVec but was declared BitVec" -- which is
 * uninformative in exactly the case the width-aware sameSort exists to catch,
 * so the check would be right and its report useless.
 *
 * The spelling deliberately matches the engine's Sort::toString
 * (include/somtparser/ir/sort.h), so a HIR sort and the sort it lowers to are
 * named identically in a diagnostic and in a dumped script.
 */
std::string toString(const Sort& s);

enum class ExprKind {
    LIT_BOOL, LIT_INT, IDENT, OP,
    /** An occurrence of a variable bound by an enclosing FORALL/EXISTS.
     *  Deliberately not an IDENT: a bound variable is not a free variable of
     *  the model, and letting one land in ConstraintModel::decls would make
     *  features() report it and make the bound-ints pass eligible to bound it
     *  (docs/languages/qdimacs.md §4.1). */
    BOUND_VAR,
    FORALL,
    EXISTS,
    /** A global constraint by name, e.g. alldifferent. Carries its arguments
     *  and is eliminated by the decompose-globals pass, which chooses between a
     *  ground and a quantified encoding per EncodingProfile::style(). */
    GLOBAL,
    /** A bit-vector constant. The value is kept as the SMT-LIB literal text
     *  (`#b1010`, `#x0a`) rather than an integer: widths are arbitrary
     *  (cryptoline.md §4.6 -- a 256-bit field element is one value), so no
     *  fixed-width C++ type can hold every one of them, and the string is what
     *  the engine's mkConstBv takes anyway. */
    LIT_BITVEC,
    LIT_STRING,
    /** A Real constant, its value kept as SMT-LIB decimal text (`1.5`, `0.1`).
     *
     *  Text and not `double`, for the reason LIT_BITVEC is text: SMT-LIB reals
     *  are exact rationals, `0.1` is not representable in binary floating
     *  point, and a translation that rounded the constants of a linear program
     *  would answer a different question while reporting Fidelity::exact().
     *  The engine's mkConstReal takes the string and its Number is GMP-backed,
     *  so the exactness survives the whole way down. */
    LIT_REAL,
    /** A floating-point constant: decimal text in Expr::name, with the format
     *  in the sort. Distinct from LIT_REAL because `1.5` as a Real and `1.5`
     *  as a Float32 are different values of different sorts -- the second is
     *  whatever RNE rounds the first to. */
    LIT_FLOAT,
    /** One of SMT-LIB's five rounding modes, its name in Expr::name (RNE, RNA,
     *  RTP, RTN, RTZ). A literal rather than an IDENT because a rounding-mode
     *  *variable* is also legal and must stay distinguishable from a constant
     *  one -- see SortKind::ROUNDING_MODE. */
    LIT_ROUNDING_MODE,
    /** One of the three nullary regular expressions -- `re.none`, `re.all`,
     *  `re.allchar` -- its name in Expr::name. A literal and not a zero-argument
     *  operator because mkOp refuses an empty argument list, which is the same
     *  reason dimacs-cnf.md §4.1's empty clause is a literal. */
    LIT_REGLAN,
    /** An application of a declared, uninterpreted function or predicate.
     *  Cluster G, wanted by TPTP, Boogie and CHC-COMP. */
    APPLY,
    /** `(as set.empty (Set T))` or `(as set.universe (Set T))`, the name in
     *  Expr::name and the set sort in Expr::sort. A literal because the two are
     *  nullary and mkOp refuses an empty argument list, and sort-annotated
     *  because neither's element sort is derivable from anything else. */
    LIT_SET,
    /** `tuple.unit`, the single value of the empty tuple sort.
     *
     *  A literal for the same reason LIT_SET is one -- it is nullary and mkOp
     *  refuses an empty argument list -- but NOT sort-annotated in the same
     *  sense: `UnitTuple` is the only sort it can have, so the sort is set by
     *  the builder rather than carried from the source. Spelling it as a
     *  zero-argument Op::TUPLE instead would have put an OP with no arguments
     *  into the IR, which every walker that reads `args[0]` to find a sort
     *  would then have to guard. */
    LIT_TUPLE_UNIT,
    /** `(cons 1 nil)` -- a datatype constructor applied to its fields. */
    DT_CONSTRUCTOR,
    /** `(hd l)` -- a selector applied to a value of its datatype. */
    DT_SELECTOR,
    /** `((_ is cons) l)` -- the tester for one constructor. Always Bool.
     *
     *  Three kinds rather than one polymorphic application, because SMT-LIB
     *  spells the tester differently from the other two and because the checks
     *  differ: a constructor takes the field sorts, a selector takes the
     *  datatype, and a tester takes the datatype and yields Bool. Collapsing
     *  them would need the checker to re-derive which it was looking at. */
    DT_TESTER,
};

enum class Op {
    AND, OR, NOT, EQ, LE, LT, GE, GT, ADD, SUB, MUL,

    /* ---- Integer division, three ways, with no default --------------------
     *
     * There is deliberately no plain `DIV`. The languages in this project do
     * not agree on what one is:
     *
     *   (-7) div 2      remainder      who spells it this way
     *   ----------      ---------      ------------------------------------
     *   -4              1              SMT-LIB `div`/`mod`, Euclidean: the
     *                                  remainder is ALWAYS non-negative
     *   -3             -1              C, Java, Go, MiniZinc `div`: truncate
     *                                  toward zero
     *   -4              1              Python `//`: floor -- which coincides
     *                                  with Euclidean here and diverges when
     *                                  the DIVISOR is negative
     *
     * All three agree on non-negative operands, which is most of every
     * benchmark suite. That is exactly what makes a default dangerous: a
     * frontend that silently inherited the wrong one would translate the
     * corpus correctly, pass its tests, and be wrong only on the instances
     * with negative dividends -- with no diagnostic, no failed round trip and
     * no fidelity entry to say so. The same failure profile as MPS's RANGES
     * sign, which is how this rule was learned.
     *
     * So a frontend must name the semantics its language actually has. Leaving
     * it out is a compile error rather than a wrong answer, and that is the
     * whole purpose of there being three names.
     *
     * MOD_* is the matching remainder in each convention; `a = b*div(a,b) +
     * mod(a,b)` holds in all three, which is what makes them a family.
     *
     * Division by zero is a SECOND axis and is not settled by picking one of
     * these. SMT-LIB makes `(div x 0)` an uninterpreted total function -- a
     * value exists and nothing constrains it -- while MiniZinc's relational
     * semantics makes the enclosing Boolean context false and C makes it
     * undefined behaviour. A frontend states its choice as an EncodingChoice
     * (ParseOutcome::report); it must not inherit SMT-LIB's by saying nothing.
     */
    DIV_EUCLID, DIV_TRUNC, DIV_FLOOR,
    MOD_EUCLID, MOD_TRUNC, MOD_FLOOR,
    /** Real division, `/`. Not one of the family above: over the reals there is
     *  no rounding to disagree about, so there is one operator and no choice to
     *  record. Division by zero remains the second axis, and remains the
     *  frontend's to state. Int operands are legal and the result is Real --
     *  `(/ 1 2)` is one half, not zero. */
    DIV_REAL,
    /** `((_ divisible n) t)`: true when t is a multiple of n. Indexed by the
     *  divisor, which is part of the operator rather than an argument -- see
     *  mkIsDivisible.
     *
     *  Expressible as `(= (mod t n) 0)`, and kept for a reason the expansion
     *  makes plain: `mod` is one of THREE conventions here, so writing the
     *  expansion means choosing one, and the choice is invisible in the result.
     *  Divisibility does not depend on it -- every convention agrees on whether
     *  the remainder is zero -- so an operator that says "divisible" says
     *  strictly less than any of its expansions, which is what makes it the
     *  honest translation. */
    IS_DIVISIBLE,
    /** n-ary exclusive or over Bool. Expressible through AND/OR/NOT, but the
     *  expansion duplicates every argument, and QCIR and QDIMACS-adjacent
     *  formats write `xor` directly -- so translating it as an expansion would
     *  make the emitted script differ in size and shape from what the source
     *  said, for no gain (docs/languages/qcir.md §4.7). */
    XOR,
    /* ---- Expressible, and still here ---------------------------------------
     *
     * Each of these four can be written with the operators above -- `=>` is
     * `(or (not a) b)`, `distinct` is pairwise `(not (= ...))`, unary `-` is
     * `(- 0 x)`, `abs` is an `ite` -- and the frontends did exactly that for a
     * while, on the argument that an IR should not carry what it can derive.
     *
     * The round trip is what settled it the other way. `text -> Parser -> HIR
     * -> Parser -> text` is the property that says a construct can be read back
     * (test/regression/test_parser_to_hir.cpp), and expansion is one-way: `=>`
     * goes in and `(or (not a) b)` comes out. The script has changed shape,
     * every measurement taken on it is a measurement of a different formula,
     * and no diagnostic says so. Expressible is not the same as representable.
     *
     * `=>` is also not a corner case. Every CHC-COMP clause is an implication
     * (docs/languages/chc-comp.md §2.2), and `distinct` is how alldifferent
     * reaches an SMT script.
     *
     * IMPLIES is binary and right-associative in SMT-LIB; it is kept binary
     * here, so an n-ary source chain is built as nested applications rather
     * than flattened into something with a different meaning.
     */
    IMPLIES,
    /** Pairwise distinct, n-ary. NOT a chain of `!=`: `(distinct a b c)` says
     *  all three differ, while `(and (!= a b) (!= b c))` permits a = c. */
    DISTINCT,
    /** Unary minus. Distinct from `SUB` so that `(- x)` round-trips as `(- x)`
     *  rather than as `(- 0 x)`. */
    NEG,
    /** `(abs x)` over Int or Real, result the argument's sort. */
    ABS,
    /** `(ite c a b)`. Result is the sort of the branches, which must agree.
     *  The standard QCIR-G14 defines ite(x,y,z) as (x AND y) OR (NOT x AND z),
     *  so an expansion is available and exact -- and duplicates the condition.
     *  Having the operator lets the frontend record which route it took. */
    ITE,
    /** SMT-LIB's array select and store. STORE is here because `select` alone
     *  is not the array theory: this header says ARRAY *is* SMT-LIB's array,
     *  and a read-only one is not that. QF_AX and every array logic need
     *  writes, and the extensionality axiom relates the two operators, so
     *  shipping one without the other left a sort whose theory was half
     *  present (docs/languages/smtlib2.md). */
    SELECT,
    /** (store a i v): the array a with index i mapped to v. Same sort as a. */
    STORE,
    /** Pointwise Boolean array maps used by finite-set encodings. */
    ARRAY_MAP_AND, ARRAY_MAP_OR, ARRAY_MAP_NOT,
    /** `((as const (Array T U)) v)`: the array mapping every index to v.
     *
     *  Indexed by its RESULT SORT and not by its argument, like int2bv: the
     *  value fixes U and says nothing about T, so `(as const (Array Int Int))`
     *  and `(as const (Array Bool Int))` applied to the same `0` are different
     *  arrays. See mkConstArray. */
    CONST_ARRAY,

    /* ---- Bit-vectors -----------------------------------------------------
     *
     * Kept apart from the arithmetic operators above rather than dispatched on
     * the argument sort, and the reason is not symmetry with SMT-LIB's
     * spelling. `bvult` and `bvslt` are two different orderings of the same
     * bits, so one Op::LT reaching a bit-vector would have to *guess* the
     * signedness. BTOR2 states it in the input -- `ult` and `slt` are distinct
     * opcodes (docs/languages/btor2.md §4.1) -- and an IR that cannot record
     * the distinction loses it at the door, producing a translation that is
     * wrong for exactly the instances that use the other one. Every signed
     * operator below therefore has an unsigned twin and vice versa.
     *
     * Division is the same story one level down: bvudiv and bvsdiv differ, and
     * bvsrem, bvsmod differ from each other in the sign of the result. The
     * engine builds all of them, so the choice is only about what the HIR can
     * say. */
    BV_NOT, BV_NEG,                                  // unary, width-preserving
    BV_AND, BV_OR, BV_XOR, BV_NAND, BV_NOR, BV_XNOR, // bitwise
    BV_ADD, BV_SUB, BV_MUL,
    BV_UDIV, BV_UREM, BV_SDIV, BV_SREM, BV_SMOD,
    BV_SHL, BV_LSHR, BV_ASHR,                        // logical/arithmetic shifts
    BV_ULT, BV_ULE, BV_UGT, BV_UGE,                  // unsigned order  -> Bool
    BV_SLT, BV_SLE, BV_SGT, BV_SGE,                  // signed order    -> Bool
    /** (concat a b): width is the sum, so this is the one non-indexed
     *  bit-vector operator whose result sort is neither Bool nor its first
     *  argument's. */
    BV_CONCAT,
    /** `(_ extract hi lo) x`. Indexed: see Expr::indices and mkBvExtract. */
    BV_EXTRACT,
    /** `(_ zero_extend n) x` / `(_ sign_extend n) x`. Indexed; see mkBvExtend.
     *  Both exist for the same reason bvult and bvslt both do: widening a
     *  bit-vector is a different function depending on whether the value is
     *  read as signed, and the source format says which. */
    BV_ZERO_EXTEND, BV_SIGN_EXTEND,
    /** `(_ rotate_left n) x` / `(_ rotate_right n) x`. Indexed, and
     *  width-preserving: a rotation moves bits rather than adding or dropping
     *  any, which is what distinguishes it from a shift.
     *
     *  Expressible -- a rotation is two shifts and an `or` -- and kept for the
     *  reason `=>` and `distinct` are: expansion is one-way. It is also not a
     *  corner case here. Rotation is the primitive of every block cipher and
     *  hash function, so it is what CryptoLine's own examples are made of
     *  (docs/languages/cryptoline.md), and a hardware format that writes one
     *  rotate would come back as three operators over a doubled term. */
    BV_ROTATE_LEFT, BV_ROTATE_RIGHT,
    /** `(_ repeat n) x`: x concatenated with itself n times, so the result is
     *  n times as wide. Indexed, and the second bit-vector operator after
     *  BV_CONCAT whose width is neither its argument's nor fixed. */
    BV_REPEAT,
    /** `(bvcomp x y)`: `#b1` when the two are equal and `#b0` otherwise.
     *
     *  The result is a ONE-BIT VECTOR, not a Bool, and that is the whole reason
     *  this is an operator rather than a spelling of `=`. bvcomp is how a
     *  circuit-shaped encoding compares two words without leaving the
     *  bit-vector sort -- its output feeds `bvand` -- and rewriting it as `(ite
     *  (= x y) #b1 #b0)` changes a term into a formula-with-a-term-inside,
     *  which is a different shape for every measurement taken on the script. */
    BV_COMP,

    /* ---- Floating point --------------------------------------------------
     *
     * The five arithmetic operators take a RoundingMode as their first
     * argument, which is where the SortKind above earns its place.
     *
     * FP_EQ is the one to be careful with, and it is why `=` is not enough.
     * `fp.eq` is IEEE-754 equality: NaN is equal to nothing including itself,
     * and +0 equals -0. SMT-LIB's `=` on Float is *structural*: NaN = NaN holds
     * and +0 = -0 does not. Both are Float x Float -> Bool, both are legal, and
     * they disagree on exactly the values floating-point bugs live at -- so
     * translating one as the other type-checks, lowers, and answers a different
     * question. A format that writes `fp.eq` must reach FP_EQ and nothing else.
     */
    FP_ADD, FP_SUB, FP_MUL, FP_DIV,       // (rm, x, y)
    FP_FMA,                               // (rm, x, y, z)
    FP_SQRT, FP_ROUND_TO_INTEGRAL,        // (rm, x)
    FP_ABS, FP_NEG,                       // (x)
    FP_REM, FP_MIN, FP_MAX,               // (x, y), no rounding mode
    FP_LEQ, FP_LT, FP_GEQ, FP_GT,         // (x, y) -> Bool
    FP_EQ,                                // IEEE equality; see above
    FP_IS_NORMAL, FP_IS_SUBNORMAL, FP_IS_ZERO, FP_IS_INFINITE,
    FP_IS_NAN, FP_IS_NEGATIVE, FP_IS_POSITIVE,

    /* ---- Strings ---------------------------------------------------------
     *
     * SMT-LIB's Unicode string theory, minus the regular-expression fragment,
     * which needs a RegLan sort and about a dozen more operators and is
     * deliberately a later slice -- see docs/languages/smtlib2.md.
     *
     * The index conventions are SMT-LIB's and are total rather than partial:
     * str.at and str.substr out of range yield the empty string, and
     * str.indexof yields -1 when the needle is absent. A frontend for a
     * language whose own strings are partial must say so rather than rely on
     * these, which is the same shape as minizinc.md §4.2's partial functions.
     */
    STR_CONCAT,                           // n-ary
    STR_LEN,                              // String -> Int
    STR_AT,                               // (s, i)      -> String
    STR_SUBSTR,                           // (s, i, n)   -> String
    STR_INDEXOF,                          // (s, t, i)   -> Int
    STR_REPLACE, STR_REPLACE_ALL,         // (s, t, u)   -> String
    STR_CONTAINS, STR_PREFIXOF, STR_SUFFIXOF,   // -> Bool
    STR_LT, STR_LE,                       // lexicographic -> Bool
    STR_TO_INT,                           // String -> Int
    STR_FROM_INT,                         // Int -> String
    STR_TO_CODE, STR_FROM_CODE,           // single-character code point
    /** `(str.is_digit s)`: true when s is a single character in `0`..`9`.
     *  String -> Bool, and not a length-and-range test in disguise -- SMT-LIB
     *  defines it on code points, so an expansion would have to name the code
     *  points and would stop being the same predicate under a different
     *  alphabet. */
    STR_IS_DIGIT,

    /* ---- Regular expressions --------------------------------------------- */
    STR_TO_RE,                            // String  -> RegLan  (the singleton)
    STR_IN_RE,                            // (String, RegLan) -> Bool
    RE_CONCAT, RE_UNION, RE_INTER, RE_DIFF,     // n-ary over RegLan
    RE_STAR, RE_PLUS, RE_OPT, RE_COMPLEMENT,    // unary
    RE_RANGE,                             // (String, String) -> RegLan
    /** `(_ re.loop i j) r`: between i and j repetitions. Indexed. */
    RE_LOOP,
    /** The three string operators that take a REGULAR EXPRESSION where their
     *  plain counterparts take a string.
     *
     *  `(str.indexof_re s r i)` is String x RegLan x Int -> Int; the two
     *  replacements are String x RegLan x String -> String. They are separate
     *  operators rather than overloads of str.indexof and str.replace because
     *  the second argument has a different SORT, and a translation that
     *  confused them would be looking for a literal where the source asked for
     *  a language. */
    STR_INDEXOF_RE, STR_REPLACE_RE, STR_REPLACE_RE_ALL,

    /* ---- Conversions between theories ------------------------------------
     *
     * Each theory was an island until these. They are the operators a real
     * benchmark reaches for at the seams -- a bit-vector used as an array
     * index, a floating-point result compared against a rational specification
     * -- and every one of them is a place a translation can silently change
     * the question, so the signed/unsigned pairs are kept apart here exactly as
     * they are for the orderings.
     */
    TO_INT,                               // Real -> Int, rounding toward -inf
    TO_REAL,                              // Int -> Real, exact
    /** `(is_int r)`: true when the Real r has an exact integer value. Real ->
     *  Bool, so it is a predicate rather than a conversion, and it lives here
     *  because SMT-LIB puts it in Reals_Ints beside the two above and because
     *  the only way to say it otherwise -- `(= r (to_real (to_int r)))` --
     *  names `to_int`, whose rounding is the thing being asked about. */
    IS_INT,
    /** Unsigned and signed readings of the same bits. bv2nat is in [0, 2^w);
     *  bv2int is in [-2^(w-1), 2^(w-1)). Choosing wrong shifts every negative
     *  value by 2^w without any diagnostic. */
    BV_TO_NAT, BV_TO_INT,
    /** `(_ int2bv w) n`. Indexed by the target width. */
    INT_TO_BV,
    FP_TO_REAL,                           // exact; undefined on NaN and inf
    FP_TO_IEEE_BV,                        // the bit pattern, width eb + sb
    /** `((_ fp.to_sbv w) rm x)` / `((_ fp.to_ubv w) rm x)`. Indexed. */
    FP_TO_SBV, FP_TO_UBV,
    /** `((_ to_fp eb sb) rm x)` from a Real, a Float or a signed bit-vector,
     *  and TO_FP_UNSIGNED from an unsigned one. Indexed by the format. */
    TO_FP, TO_FP_UNSIGNED,
    /** `((_ to_fp eb sb) bv)` with NO rounding mode: reinterprets the bit
     *  pattern as a float -- the inverse of FP_TO_IEEE_BV, not a rounding
     *  conversion (rounding a bit pattern read as an integer is not reading
     *  it as a float). Indexed by the format. */
    IEEE_BV_TO_FP,

    /* ---- Finite sets -----------------------------------------------------
     *
     * The theory the engine did not have until 2026-08-12: it carried a
     * SORT_KIND for sets and zero operators, so `(Set Int)` was a sort a model
     * could declare and nothing could constrain. MiniZinc's `var set of int` is
     * the producer this exists for (docs/languages/minizinc.md §2.3).
     *
     * Note the argument orders, both of which are SMT-LIB's and both of which
     * read backwards: `set.member` takes the ELEMENT first, and `set.insert`
     * takes the set LAST.
     */
    SET_SINGLETON,                        // T -> (Set T)
    SET_UNION, SET_INTER,                 // n-ary
    SET_MINUS,                            // binary
    SET_MEMBER,                           // (T, Set T) -> Bool
    SET_SUBSET,                           // (Set T, Set T) -> Bool
    SET_CARD,                             // (Set T) -> Int
    SET_INSERT,                           // (T..., Set T) -> Set T
    SET_COMPLEMENT,

    /* ---- Tuples ----------------------------------------------------------
     *
     * The same shape as the sets above, and found the same way: the engine
     * carried five NODE_KINDs, a SORT_KIND, builders and a printer for tuples,
     * and the HIR had no sort for one -- so every script that so much as
     * declared `(Tuple Int Bool)` failed at its declaration and not one
     * operator was ever reached (docs/languages/smtlib2.md §4.6). A table
     * cannot be checked against a vocabulary that has no word for its
     * arguments.
     *
     * Three of the four are INDEXED -- `((_ tuple.select i) t)` -- so the
     * index lives in Expr::indices and not in the arguments: it says WHICH
     * projection is applied, not what it is applied to, which is the same
     * distinction `(_ extract hi lo)` makes. The engine spells them as
     * constant CHILDREN, so the lift and the lowering each have to move them
     * across, and none of the three can be a table entry.
     */
    TUPLE,                                // T1...Tn -> (Tuple T1 ... Tn)
    TUPLE_SELECT,                         // indexed by i: (Tuple ...) -> Ti
    TUPLE_UPDATE,                         // indexed by i: (Tuple ..., Ti) -> (Tuple ...)
    TUPLE_PROJECT,                        // indexed by i...: (Tuple ...) -> (Tuple ...)
};

/** Is @p op one of the bit-vector operators? Exported because lowering has to
 *  route them to a different family of builders, and a second hand-written
 *  enumeration in that file would drift from this one. */
bool isBitVecOp(Op op);
/** Is @p op one of the floating-point operators? Same reason as isBitVecOp:
 *  lowering routes them to a different family of builders. */
bool isFloatOp(Op op);
/** Is @p op one of the string operators? */
bool isStringOp(Op op);
/** Is @p op one of the regular-expression operators? */
bool isRegexOp(Op op);
/** Is @p op one of the cross-theory conversions? */
bool isConversionOp(Op op);
/** Is @p op one of the finite-set operators? */
bool isSetOp(Op op);
/** Is @p op one of the tuple operators? Same reason as isSetOp: the lowering
 *  routes them to their own family of builders, and a second hand-written
 *  enumeration there would drift from this one. */
bool isTupleOp(Op op);

struct Expr;
using ExprPtr = std::shared_ptr<const Expr>;

/** A variable introduced by a quantifier. */
struct Binder {
    std::string name{};
    Sort        sort;
};

struct Expr {
    // Releasing the last root of an immutable DAG must not recurse through its
    // operands. Shared descendants owned elsewhere remain untouched.
    ~Expr() noexcept;

    ExprKind             kind = ExprKind::LIT_BOOL;
    Sort                 sort;
    Op                   op = Op::AND;      // valid when kind == OP
    bool                 bool_value = false;// valid when kind == LIT_BOOL
    /** LIT_INT, and valid ONLY when the literal fits -- ask fitsInt64 first.
     *
     *  The authoritative value is the decimal text in `name`. An OPB
     *  coefficient is an unbounded integer by explicit design and the format
     *  document's own example exceeds LLONG_MAX
     *  (docs/languages/opb-wbo.md §2.3), so `long long` is a limit of this
     *  field and not of the language.
     *
     *  Deliberately NOT a second ExprKind. SMT-LIB has one numeral syntax and a
     *  big integer is the same literal with a bigger value; a `LIT_BIGINT`
     *  would put a C++ limitation into the IR's vocabulary and oblige every
     *  consumer to handle two kinds forever -- with the drift that some handle
     *  one and not the other, which is exactly what isConstant did to
     *  LIT_BITVEC before it was fixed. */
    long long            int_value = 0;
    std::string          name;              // IDENT, BOUND_VAR, GLOBAL, LIT_INT
    std::vector<ExprPtr> args;              // OP, GLOBAL; body[0] for FORALL/EXISTS
    std::vector<Binder>  binders;           // FORALL, EXISTS
    /** Numeric parameters of an *indexed* operator: SMT-LIB's `(_ extract hi
     *  lo)` and `(_ zero_extend n)` take their indices in the identifier, not
     *  as arguments, because they are part of which function is being applied
     *  rather than what it is applied to. Storing them as ordinary args would
     *  make `(_ extract 7 0) x` a three-argument operator whose first two
     *  arguments must be literals -- a constraint no rule table can state.
     *  Empty for every non-indexed operator. */
    std::vector<unsigned> indices;
    SourceLoc            loc;
};

/* Each builder takes an optional source location. Pass one wherever the
 * frontend knows it: Uir::Hir::typeCheck reports against Expr::loc and falls
 * back to the enclosing item's location only when the expression has none, so
 * a frontend that omits it turns "line 7, column 12: 'b' is used as Bool" into
 * a message pointing at the whole constraint. */
ExprPtr mkBool(bool v, SourceLoc loc = {});
ExprPtr mkInt(long long v, SourceLoc loc = {});
/** An integer literal of unbounded magnitude, from its decimal text.
 *  Expr::int_value is filled in when the value fits and is meaningless
 *  otherwise; fitsInt64 is how a caller finds out. */
ExprPtr mkInt(std::string decimal, SourceLoc loc = {});
/** Does @p e's integer literal fit in Expr::int_value?
 *
 *  A consumer that needs the machine integer must ask. Reading int_value
 *  unconditionally on a wide literal would silently use a wrong number, which
 *  is the failure this text-backed representation exists to prevent. */
bool fitsInt64(const Expr& e);
ExprPtr mkIdent(std::string name, Sort sort, SourceLoc loc = {});
/** Result sort is derived: comparisons and connectives are Bool, arithmetic
 *  takes the widest argument sort. Whether the arguments *may* carry those
 *  sorts is not checked here -- see hir/typecheck.h. */
ExprPtr mkOp(Op op, std::vector<ExprPtr> args, SourceLoc loc = {});

/** An occurrence of a quantifier-bound variable. */
ExprPtr mkBoundVar(std::string name, Sort sort, SourceLoc loc = {});
/** `forall binders. body` / `exists binders. body`. Both are Bool. */
ExprPtr mkForall(std::vector<Binder> binders, ExprPtr body, SourceLoc loc = {});
ExprPtr mkExists(std::vector<Binder> binders, ExprPtr body, SourceLoc loc = {});
/** A high-level relation or value applied to arguments. Most globals return
 *  Bool; count_value returns Int. Each signature is checked by typecheck.h. */
ExprPtr mkGlobal(std::string name, std::vector<ExprPtr> args, SourceLoc loc = {});
/** A bit-vector constant. @p literal is SMT-LIB text (`#b…` or `#x…`). */
ExprPtr mkBitVec(std::string literal, unsigned width, SourceLoc loc = {});
/** `(_ extract hi lo) x`, of width hi - lo + 1. Indexed operators get their own
 *  builders because mkOp's signature has nowhere to put the indices; whether
 *  hi >= lo and both are inside @p x's width is checked by hir/typecheck.h. */
ExprPtr mkBvExtract(ExprPtr x, unsigned hi, unsigned lo, SourceLoc loc = {});
/** `(_ zero_extend n) x` or `(_ sign_extend n) x`, of width w + n.
 *  @p op must be BV_ZERO_EXTEND or BV_SIGN_EXTEND. */
ExprPtr mkBvExtend(Op op, ExprPtr x, unsigned by, SourceLoc loc = {});
/** `(_ rotate_left n) x` / `(_ rotate_right n) x`.
 *  @p op must be BV_ROTATE_LEFT or BV_ROTATE_RIGHT. */
ExprPtr mkBvRotate(Op op, ExprPtr x, unsigned by, SourceLoc loc = {});
/** `(_ repeat n) x`. @p times is n; the result is n times as wide as @p x. */
ExprPtr mkBvRepeat(ExprPtr x, unsigned times, SourceLoc loc = {});
/** `((_ divisible n) t)`. @p by is n, and must be positive -- SMT-LIB requires
 *  n in N>0, and divisibility by zero is not a weaker question but a different
 *  one. The checker reports a zero rather than this builder aborting on it. */
ExprPtr mkIsDivisible(ExprPtr t, unsigned by, SourceLoc loc = {});
ExprPtr mkString(std::string value, SourceLoc loc = {});
/** A Real constant from decimal text (`1.5`) or exact rational text (`1/3`).
 *  Kept exact; see ExprKind::LIT_REAL for why this is not a double, and
 *  docs/languages/lp.md §4.1 for why the rational form is needed as well --
 *  1/3 has no decimal spelling and rounding it answers a different question. */
ExprPtr mkReal(std::string decimal_or_rational, SourceLoc loc = {});
/** A floating-point constant of format (eb, sb) from decimal text. */
ExprPtr mkFloat(std::string decimal, unsigned exponent, unsigned significand,
                SourceLoc loc = {});
/** One of SMT-LIB's five rounding modes. @p mode must be RNE, RNA, RTP, RTN or
 *  RTZ; anything else is refused by hir/typecheck.h rather than passed through,
 *  because the engine's builder takes the name as a string and an unrecognised
 *  one would reach the emitted script. */
ExprPtr mkRoundingMode(std::string mode, SourceLoc loc = {});
/** `(as set.empty (Set T))` / `(as set.universe (Set T))`. @p name must be
 *  "set.empty" or "set.universe"; @p set_sort must be a set sort. */
ExprPtr mkSetConst(std::string name, Sort set_sort, SourceLoc loc = {});
/** One of `re.none`, `re.all`, `re.allchar`. Refused by hir/typecheck.h if it is
 *  not one of those three. */
ExprPtr mkReglanConst(std::string name, SourceLoc loc = {});
/** `(_ re.loop lo hi) r`. */
ExprPtr mkReLoop(ExprPtr r, unsigned lo, unsigned hi, SourceLoc loc = {});
/** `(_ int2bv w) n`. */
ExprPtr mkIntToBv(ExprPtr n, unsigned width, SourceLoc loc = {});
/** `((as const (Array T U)) v)`. @p array_sort must be an array sort, and its
 *  element sort is what @p value must have -- neither is derivable from the
 *  value alone, which is why this cannot be an mkOp. */
ExprPtr mkConstArray(Sort array_sort, ExprPtr value, SourceLoc loc = {});
/** `((_ fp.to_sbv w) rm x)` / `((_ fp.to_ubv w) rm x)`.
 *  @p op must be FP_TO_SBV or FP_TO_UBV. */
ExprPtr mkFpToBv(Op op, ExprPtr rm, ExprPtr x, unsigned width, SourceLoc loc = {});
/** `((_ to_fp eb sb) rm x)` / `((_ to_fp_unsigned eb sb) rm x)`.
 *  @p op must be TO_FP or TO_FP_UNSIGNED. */
ExprPtr mkToFp(Op op, ExprPtr rm, ExprPtr x, unsigned exponent,
               unsigned significand, SourceLoc loc = {});
/** `((_ to_fp eb sb) bv)` -- the bit-pattern reinterpretation, the inverse of
 *  FP_TO_IEEE_BV. The argument must be a bit-vector of width exponent +
 *  significand; the checker enforces that, this builder does not. */
ExprPtr mkIeeeBvToFp(ExprPtr x, unsigned exponent, unsigned significand,
                     SourceLoc loc = {});
/** `tuple.unit`, the one value of `UnitTuple`.
 *
 *  Separate from mkOp(Op::TUPLE, {}) because mkOp refuses an empty argument
 *  list -- and separate from `mkTuple` below so that the empty case cannot be
 *  reached by accident: a frontend that folded an empty container into
 *  `(tuple)` would produce the unit tuple silently, where it almost certainly
 *  meant an empty SET or an empty list. */
ExprPtr mkTupleUnit(SourceLoc loc = {});
/** `(tuple t1 ... tn)`, of sort `(Tuple T1 ... Tn)`. @p fields must be
 *  non-empty; the nullary tuple is mkTupleUnit(). */
ExprPtr mkTuple(std::vector<ExprPtr> fields, SourceLoc loc = {});
/** `((_ tuple.select i) t)`, of @p t's i-th field sort.
 *
 *  Indexed, so it gets a builder for the reason mkBvExtract does. Whether
 *  @p t is a tuple at all and whether @p index is inside its arity are checked
 *  by hir/typecheck.h -- this builder records Bool for a malformed argument
 *  rather than aborting, which is what keeps a bad script a diagnostic instead
 *  of a crash. */
ExprPtr mkTupleSelect(ExprPtr t, unsigned index, SourceLoc loc = {});
/** `((_ tuple.update i) t v)`, of @p t's own sort. */
ExprPtr mkTupleUpdate(ExprPtr t, unsigned index, ExprPtr value, SourceLoc loc = {});
/** `((_ tuple.project i1 ... ik) t)`, of sort `(Tuple Ti1 ... Tik)`.
 *
 *  An EMPTY index list is legal and yields `UnitTuple` -- it is the projection
 *  onto no fields, which SMT-LIB permits and which is not the same thing as a
 *  malformed projection. */
ExprPtr mkTupleProject(ExprPtr t, std::vector<unsigned> indices, SourceLoc loc = {});
/** An application of a declared function. The result sort is the declaration's;
 *  whether the arguments match its signature is checked by hir/typecheck.h. */
ExprPtr mkApply(std::string name, Sort result, std::vector<ExprPtr> args,
                SourceLoc loc = {});

/** @p e with every free IDENT renamed by @p names, and its sort taken from
 *  @p sorts when that map has an entry for the ORIGINAL name.
 *
 *  This exists because three frontends wrote it separately and all three got it
 *  wrong the same way. Renaming a term means rebuilding it, and rebuilding an
 *  OP through mkOp **drops the indices**: `(_ extract 7 0) x` came back as a
 *  bare extract with no indices, and `((as const (Array T U)) v)` -- whose sort
 *  is not derivable from its argument at all -- aborted in mkOp rather than
 *  being rebuilt. So this copies the node and replaces only its arguments,
 *  which cannot forget a field that mkOp's signature has nowhere to put, and
 *  cannot start forgetting one that Expr gains later.
 *
 *  It also descends where those three stopped. They returned any non-OP node
 *  unchanged, so a GLOBAL's arguments and a quantifier's body were never
 *  renamed -- silently, producing a smaller substitution that still
 *  type-checked. And a binder SHADOWS: a quantifier binding a name in @p names
 *  removes it inside its own body, because that occurrence is a different
 *  variable.
 *
 *  Substitution is capture-avoiding only in the sense that shadowing is
 *  respected; it does not rename binders to dodge a collision, because every
 *  caller maps free variables to fresh names it just minted. */
ExprPtr substituteIdents(const ExprPtr& e,
                         const std::unordered_map<std::string, std::string>& names,
                         const std::unordered_map<std::string, Sort>& sorts = {});
/** `(cons 1 nil)`. @p result is the datatype sort the constructor belongs to. */
ExprPtr mkDtConstructor(std::string name, Sort result, std::vector<ExprPtr> args,
                        SourceLoc loc = {});
/** `(hd l)`. @p result is the selector's field sort. */
ExprPtr mkDtSelector(std::string name, Sort result, ExprPtr value,
                     SourceLoc loc = {});
/** `((_ is cons) l)`. Always Bool. */
ExprPtr mkDtTester(std::string constructor_name, ExprPtr value, SourceLoc loc = {});

/** A declared function or predicate, uninterpreted or exactly defined. A
 *  predicate is a function whose result sort is Bool -- SMT-LIB makes no
 *  distinction and neither does this, which lets one signature serve TPTP's
 *  predicates and Boogie's functions. */
struct FunDecl {
    std::string       name;
    std::vector<Sort> params;      // empty: a nullary function/constant
    Sort              result;
    SourceLoc         loc;
    /** Optional formal names for an exact, non-recursive definition. When
     *  `body` is present, this list must match `params` in length and sort;
     *  BOUND_VAR occurrences in the body refer to these binders. Appended to
     *  preserve existing aggregate initializers. */
    std::vector<Binder> binders{};
    /** Null means uninterpreted declaration; otherwise this function's exact
     *  body. Cycles are rejected unless every member of the recursive call
     *  component has the same non-empty `recursive_group` label. Such a group
     *  denotes equations in SMT-LIB `define-funs-rec`; this API does not prove
     *  structural termination or uniqueness of a total function. */
    ExprPtr           body{};
    /** A target-only helper: it is defined in the target signature but is not
     *  an observable/source symbol in translation contracts or projections. */
    bool              auxiliary = false;
    /** Explicit opt-in label for one mutually recursive equation group.
     *  Empty preserves the default acyclic-definition contract. */
    std::string       recursive_group{};
};

/** One field of a constructor: SMT-LIB's selector. */
struct DtSelector {
    std::string name{};
    Sort        sort;
};

struct DtConstructor {
    std::string             name;
    std::vector<DtSelector> selectors;   // empty: a nullary constructor
};

/**
 * `(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))`.
 *
 * Recursive by construction: a selector's sort may be the datatype being
 * declared, which is what makes lists and trees expressible and what a frontend
 * for TPTP or SMT-LIB's ADT logics needs. Mutually recursive groups are one
 * declaration each here; the engine's declare-datatypes takes a group, and
 * lowering emits them in declaration order.
 */
struct DatatypeDecl {
    std::string                name;
    /** Sort parameters, in declaration order; empty for an ordinary datatype.
     *
     *  SMT-LIB writes them as `(par (X) ...)` and they are the datatype's
     *  ARITY as well as its parameter names. The names are carried rather than
     *  just the count because a selector's sort mentions them -- `hd : X` --
     *  and because the lowering has to write the same `par` form back. */
    std::vector<std::string>   params;
    std::vector<DtConstructor> constructors;
    SourceLoc                  loc;
    /** cvc5's declare-codatatypes: potentially infinite constructor trees. */
    bool                       coinductive = false;
};

/** A free SMT sort constructor from `(declare-sort S arity)`. Keep this
 *  separate from uses of `SortKind::UNINTERPRETED`: a model may use an
 *  undeclared/inferred sort for legacy frontends, while this record preserves
 *  an explicit declaration even when no term mentions it. */
struct UninterpretedSortDecl {
    std::string name{};
    std::size_t arity = 0;
    SourceLoc   loc;
};

struct VarDecl {
    std::string name{};
    Sort        sort;
    ExprPtr     lower_bound;   // optional
    ExprPtr     upper_bound;   // optional
    SourceLoc   loc;
    /** Introduced by a semantics-preserving encoding rather than declared by
     *  the source program. Auxiliary variables belong to the target signature
     *  but are deliberately omitted by the source-model projection beta. */
    bool        auxiliary = false;
};

struct Constraint {
    ExprPtr     formula;
    bool        soft = false;
    /** Cost of violating a soft constraint. Valid only when `weight_text` is
     *  empty -- see below. */
    double      weight = 1.0;
    /** The weight as decimal text, authoritative when non-empty.
     *
     *  The same decision as Expr::int_value's, for the same reason one layer
     *  over: WBO soft costs are big integers by explicit design
     *  (docs/languages/opb-wbo.md §2.3), and a `double` loses them -- 10^23
     *  round-trips through a double as scientific notation, which is not a
     *  numeral and which the engine's builder rejects. A frontend with an exact
     *  cost writes it here; one with a fractional weight uses the double. */
    std::string weight_text;
    std::string group;
    SourceLoc   loc;
};

enum class ObjKind { MINIMIZE, MAXIMIZE };

/**
 * How several objectives combine.
 *
 * Multi-objective optimisation is OMT's own vocabulary, not one language's
 * quirk: this engine's command dispatch already reads lex-optimize,
 * pareto-optimize, box-optimize, minmax and maxmin
 * (src/frontend/base_parser.cpp), and OPT_KIND
 * (include/somtparser/frontend/objective.h) carries all five. A frontend for an
 * OMT format therefore has something to say here, and until this enum existed
 * it had nowhere to say it.
 *
 * Leaving it unsaid was not neutral. A list of objectives with no combination
 * emitted several (minimize t) commands, and Z3's documented default for those
 * is *lexicographic* -- so the pipeline was not dropping the combination, it was
 * silently choosing one. SINGLE is therefore only legal with fewer than two
 * objectives; Uir::Hir::typeCheck enforces that, so a frontend that means
 * "several independent optima" has to write BOX rather than say nothing.
 */
enum class ObjectiveCombination {
    SINGLE,          // zero or one objective
    LEXICOGRAPHIC,   // optimise the first, then the second among its optima
    PARETO,          // the non-dominated frontier
    BOX,             // each objective optimised independently
    MINMAX,          // minimise the largest
    MAXMIN,          // maximise the smallest
};

const char* objectiveCombinationName(ObjectiveCombination c);

struct Objective {
    ObjKind     kind = ObjKind::MINIMIZE;
    ExprPtr     term;
    std::string name{};
    SourceLoc   loc;
};

struct SetSolverRequirements {
    bool has_sets = false;
    bool has_quantifiers = false;
    // True includes definitely-infinite and conservatively unknown carriers.
    bool infinite_or_unknown_carrier = false;
    // The current Z3 finite-set encoding is specialized to integer elements.
    // Track this from typed HIR, including implicit singleton result sorts.
    bool non_integer_carrier = false;
};

/** A generated contiguous declaration interval, stored without one VarDecl/name
 * per coordinate. Names are `prefix + decimal(index)`, with a Bool sort in the
 * initial compact-clause API. */
struct BoolVarRange {
    std::string prefix;
    std::uint64_t first = 1;
    std::uint64_t count = 0;
    Sort sort = Sort::boolean();
    SourceLoc loc;

    bool contains(const std::string& name, std::uint64_t* index = nullptr) const;
    std::string name(std::uint64_t offset) const;
};

/** Finite indexed scalar declarations, with the same per-coordinate identity
 * as ordinary VarDecl entries. No SMT array or implicit outside coordinates
 * are introduced. The initial writer supports integer intervals and names
 * prefix + decimal(first + offset) + suffix, with prefix ending '[' and ']'
 * as suffix. Multidimensional arrays use one range per final dimension. */
struct ScalarVarRange {
    std::string prefix;
    std::uint64_t first = 0;
    std::uint64_t count = 0;
    Sort sort = Sort::integer();
    SourceLoc loc;
    std::string suffix = "]";
    ExprPtr lower_bound;
    ExprPtr upper_bound;

    bool contains(const std::string& symbol, std::uint64_t* index = nullptr) const;
    std::string name(std::uint64_t offset) const;
};

/** A typed argument in a packed function application. Range IDs index
 * scalar_var_ranges; the two reserved IDs denote an ordinary declaration or
 * a literal in the enclosing batch's constant pool. */
struct PackedScalarArgument {
    static constexpr std::uint64_t DECLARATION = UINT64_MAX;
    static constexpr std::uint64_t CONSTANT = UINT64_MAX - 1;
    std::uint64_t source = DECLARATION;
    std::uint64_t offset = 0;
};

/** Every consecutive arity-sized argument span denotes one asserted Boolean
 * APPLY. Functions remain ordinary checked HIR definitions. No expressions
 * or source-variable observables are discarded by storing their calls here. */
struct PackedFunctionCallBatch {
    std::string function;
    std::size_t arity = 0;
    SourceLoc loc;
    std::vector<ExprPtr> constants;
    std::vector<PackedScalarArgument> arguments;
};

struct PackedFunctionCalls {
    std::vector<PackedFunctionCallBatch> batches;
};

/** Exact packed clause batch. Each clause is the OR of its signed 1-based
 * literal IDs; an empty weight span means hard, otherwise it is the exact
 * positive decimal soft weight. Source file is shared, line is clause-aligned. */
struct PackedBoolClauseBatch {
    std::size_t variable_range = 0;
    std::string source_file;
    std::vector<std::uint64_t> clause_offsets;
    std::vector<std::int64_t> literals;
    std::vector<std::uint64_t> weight_offsets;
    std::string weight_bytes;
    std::vector<std::uint32_t> source_lines;
};

/** A packed numeric row has the same semantics as a Bool comparison over a
 * real linear sum. RANGE denotes lower <= sum && sum <= upper. Pool entries
 * are exact canonical finite decimals; terms index the ordinary declaration
 * vector, whose Int/Real sorts and bounds remain authoritative. */
enum class LinearRowRelation : std::uint8_t { LE, GE, EQ, RANGE };
struct PackedLinearTerm {
    std::uint64_t column = 0;
    std::uint64_t coefficient = 0;
};
struct PackedLinearRow {
    std::uint64_t begin = 0;
    std::uint64_t end = 0;
    std::uint64_t rhs = 0;       // lower endpoint for RANGE
    std::uint64_t upper = 0;     // used only by RANGE
    std::uint32_t source_line = 0;
    LinearRowRelation relation = LinearRowRelation::EQ;
};
struct PackedLinearRowBatch {
    std::string source_file;
    std::vector<PackedLinearRow> rows;
    std::vector<PackedLinearTerm> terms;
};
struct PackedLinearRows {
    std::vector<std::string> numbers;
    std::vector<PackedLinearRowBatch> batches;
};

struct ConstraintModel {
    std::vector<VarDecl>    decls;
    /** Uninterpreted functions and predicates in scope. Kept apart from `decls`
     *  because a function is not a variable: features() must not report it as
     *  one, and the bound-ints pass iterates decls. */
    std::vector<FunDecl>    funs;
    /** Algebraic datatypes in scope, in declaration order. A selector may name
     *  a datatype declared later in the list, so the whole list is registered
     *  before any constructor is checked. */
    std::vector<DatatypeDecl> datatypes;
    std::vector<Constraint> constraints;
    std::vector<Objective>  objectives;
    /** Required to be something other than SINGLE once `objectives` holds two
     *  or more. See ObjectiveCombination. */
    ObjectiveCombination    objective_combination = ObjectiveCombination::SINGLE;
    /** Explicit free sort constructors, in source declaration order. Appended
     *  to preserve positional aggregate initialization of the earlier fields. */
    std::vector<UninterpretedSortDecl> uninterpreted_sorts;
    /** Compact generated declarations and clauses. Appended to preserve the
     * positional aggregate layout used by existing HIR clients. */
    std::vector<BoolVarRange> bool_var_ranges;
    std::vector<PackedBoolClauseBatch> packed_bool_clauses;
    /** Immutable shared storage makes HIR snapshots cheap. Numeric rows are
     * segmented so construction never reallocates the whole matrix at once. */
    std::shared_ptr<const PackedLinearRows> packed_linear_rows;
    std::vector<ScalarVarRange> scalar_var_ranges;
    std::shared_ptr<const PackedFunctionCalls> packed_function_calls;

    /** The deepest quantifier alternation on any path through the model; see
     *  Uir::Stats::max_quantifier_alternations for why it is worth reporting. */
    std::size_t maxQuantifierAlternations() const;

    /** High-level features actually present. The pass manager validates the
     *  configured pipeline against this set before running anything. */
    std::unordered_set<Feature, Feature::Hash> features() const;
    /** Solver-only semantic requirements; deliberately separate from pass
     *  features because Set lowers natively and is not a pipeline obligation. */
    SetSolverRequirements setSolverRequirements() const;
};

using ConstraintModelPtr = std::shared_ptr<ConstraintModel>;

} // namespace SOMTParser::Uir::Hir

#endif /* SOMTPARSER_HIR_HIR_HEADER */
