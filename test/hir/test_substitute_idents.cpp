// Renaming a term must not quietly make it a different term.
//
// Three frontends -- MoXI, VMT-LIB and Boogie -- each need to rewrite a formula
// with its variables renamed: to a step of an unrolling, to an SSA version. All
// three wrote the same recursion, and all three had the same two defects,
// because a hand-written rebuild is a table and a table gets forgotten.
//
//   1. **Rebuilding an OP through `mkOp` DROPS THE INDICES.** `(_ extract 7 0)`
//      carries its 7 and 0 in the identifier rather than as arguments, and
//      `mkOp`'s signature has nowhere to put them -- so the rebuilt term was an
//      extract of nothing in particular. `((as const (Array T U)) v)` is worse:
//      its sort is not derivable from its argument at all, so `mkOp` aborted,
//      and a MoXI file using a constant array crashed the frontend rather than
//      being translated.
//
//   2. **They stopped at OP.** Every one returned a non-OP node unchanged, so
//      the arguments of a `GLOBAL` and of an `APPLY`, and the body of a
//      quantifier, were never renamed. Nothing failed: the substitution was
//      simply smaller than asked for, and what came out still type-checked. A
//      state variable under an uninterpreted function kept the name it had at
//      step 0 for every step of the unrolling.
//
// `substituteIdents` replaces all three. It copies the node and swaps only the
// arguments -- which is the point. A copy cannot forget a field that `mkOp` has
// nowhere to put, and cannot *start* forgetting one that `Expr` gains later,
// which a rebuild would.
//
// The third property is shadowing, which none of the three needed but any
// caller can now hit: a quantifier binding a name being renamed must not have
// its body rewritten, because that occurrence is a different variable.

#include "somtparser/hir/hir.h"

#include <iostream>
#include <string>
#include <unordered_map>

#include "test_helpers.h"

using namespace SOMTParser;
namespace H = Uir::Hir;

namespace {

std::unordered_map<std::string, std::string> xToY() {
    return {{"x", "y"}};
}

/** Every IDENT name in @p e, in traversal order. */
void namesOf(const H::ExprPtr& e, std::vector<std::string>& out) {
    if (!e) { return; }
    if (e->kind == H::ExprKind::IDENT) { out.push_back(e->name); }
    for (const H::ExprPtr& a : e->args) { namesOf(a, out); }
}

bool renames(const H::ExprPtr& before) {
    const H::ExprPtr after = H::substituteIdents(before, xToY());
    std::vector<std::string> ns;
    namesOf(after, ns);
    for (const std::string& n : ns) {
        if (n == "x") { return false; }
    }
    for (const std::string& n : ns) {
        if (n == "y") { return true; }
    }
    return false;
}

} // namespace

int main() {
    std::cout << "======= substituteIdents =======\n";

    const H::Sort bv8 = H::Sort::bitvec(8);
    const H::ExprPtr x = H::mkIdent("x", bv8);

    // ---- Indexed operators keep their indices. ------------------------------
    {
        // The defect: `mkOp(e->op, args)` gave back an extract with an empty
        // index vector. Asserted on the indices themselves, because a term with
        // the right operator and the wrong indices is still a well-formed term
        // of the wrong width -- it would not fail anywhere downstream.
        const H::ExprPtr e = H::mkBvExtract(x, 7, 4);
        const H::ExprPtr r = H::substituteIdents(e, xToY());
        VERIFY(r->op == e->op);
        VERIFY(r->indices == e->indices);
        VERIFY(r->indices.size() == 2);
        VERIFY(r->indices[0] == 7 && r->indices[1] == 4);
        VERIFY(H::sameSort(r->sort, e->sort));
        VERIFY(r->args.size() == 1 && r->args[0]->name == "y");
    }
    {
        const H::ExprPtr e = H::mkBvExtend(H::Op::BV_ZERO_EXTEND, x, 8);
        const H::ExprPtr r = H::substituteIdents(e, xToY());
        VERIFY(r->indices == e->indices);
        VERIFY(H::sameSort(r->sort, e->sort));   // width 16, not 8
        VERIFY(renames(e));
    }
    {
        const H::ExprPtr e = H::mkBvRotate(H::Op::BV_ROTATE_LEFT, x, 3);
        const H::ExprPtr r = H::substituteIdents(e, xToY());
        VERIFY(r->indices == e->indices);
        VERIFY(renames(e));
    }
    {
        const H::ExprPtr e = H::mkBvRepeat(x, 4);
        const H::ExprPtr r = H::substituteIdents(e, xToY());
        VERIFY(r->indices == e->indices);
        VERIFY(H::sameSort(r->sort, e->sort));
    }
    {
        const H::ExprPtr e = H::mkIsDivisible(H::mkIdent("x", H::Sort::integer()), 3);
        const H::ExprPtr r = H::substituteIdents(e, xToY());
        VERIFY(r->indices == e->indices);
        VERIFY(renames(e));
    }

    // ---- A constant array's sort is not derivable, so it must be COPIED. ----
    {
        // This one did not merely lose information -- `mkOp` condAsserts on
        // CONST_ARRAY, so renaming a constant array threw, and a file
        // containing one reported `E_INTERNAL` from inside the frontend.
        const H::Sort arr = H::Sort::array(bv8, bv8);
        const H::ExprPtr e = H::mkConstArray(arr, x);
        const H::ExprPtr r = H::substituteIdents(e, xToY());   // must not throw
        VERIFY(r->op == H::Op::CONST_ARRAY);
        VERIFY(H::sameSort(r->sort, arr));
        VERIFY(r->args.size() == 1 && r->args[0]->name == "y");
    }

    // ---- The kinds that have arguments and are not OP. ---------------------
    {
        // A GLOBAL carries its arguments, and every one of the three
        // implementations returned it untouched.
        const H::ExprPtr e = H::mkGlobal("alldifferent", {x, H::mkIdent("z", bv8)});
        VERIFY(renames(e));
        const H::ExprPtr r = H::substituteIdents(e, xToY());
        VERIFY(r->name == "alldifferent");         // the global's own name is not a variable
        VERIFY(r->args.size() == 2);
        VERIFY(r->args[1]->name == "z");           // and the others are left alone
    }
    {
        // An APPLY likewise. Its NAME is a function symbol, not a variable, so
        // renaming a variable that happens to share the name must not touch it.
        const H::ExprPtr e = H::mkApply("f", H::Sort::boolean(), {x});
        VERIFY(renames(e));
        const H::ExprPtr f_named_x = H::mkApply("x", H::Sort::boolean(), {});
        const H::ExprPtr r = H::substituteIdents(f_named_x, xToY());
        VERIFY(r->name == "x");
    }
    {
        // A quantifier's body, where the bound variable is a different name.
        const H::ExprPtr body =
            H::mkOp(H::Op::EQ, {H::mkBoundVar("i", H::Sort::integer()),
                                H::mkIdent("x", H::Sort::integer())});
        const H::ExprPtr e = H::mkForall({{"i", H::Sort::integer()}}, body);
        VERIFY(renames(e));
        const H::ExprPtr r = H::substituteIdents(e, xToY());
        VERIFY(r->kind == H::ExprKind::FORALL);
        VERIFY(r->binders.size() == 1 && r->binders[0].name == "i");
    }

    // ---- A binder SHADOWS -- and the HIR mostly makes that automatic. -------
    {
        // `(forall ((x Int)) (= x 0))` where the map renames a free `x`. The
        // occurrence inside is a BOUND_VAR, and substituteIdents renames only
        // IDENT, so this is right for a reason that has nothing to do with
        // shadowing logic: the HIR gives a bound variable its own ExprKind
        // precisely so it cannot be mistaken for a free one.
        //
        // Recorded because a breakage probe proved it: deleting the binder
        // erasure from substituteIdents leaves this case passing. It is NOT the
        // discriminating test for shadowing, and asserting it as though it were
        // would credit the guard with a correctness the kind system supplies.
        const H::ExprPtr body =
            H::mkOp(H::Op::EQ, {H::mkBoundVar("x", H::Sort::integer()),
                                H::mkInt(0)});
        const H::ExprPtr e = H::mkForall({{"x", H::Sort::integer()}}, body);
        VERIFY(H::substituteIdents(e, xToY()) == e);
    }
    {
        // The case the erasure DOES decide: an IDENT under a binder of the same
        // name. A frontend that writes this has built a term it should have
        // built with mkBoundVar -- but the binder is right there in the node, so
        // the name is bound whatever kind the occurrence was given, and renaming
        // it would move a bound variable out of its own scope. Refusing to
        // rewrite is the reading that cannot silently change what the term says.
        const H::ExprPtr shadowed =
            H::mkForall({{"x", H::Sort::integer()}},
                        H::mkOp(H::Op::EQ, {H::mkIdent("x", H::Sort::integer()),
                                            H::mkInt(0)}));
        VERIFY(H::substituteIdents(shadowed, xToY()) == shadowed);
    }
    {
        // Shadowing is per-binder, not per-term: the same free `x` OUTSIDE the
        // quantifier is still renamed, so the erasure is scoped to the body it
        // was erased for and does not leak to the rest of the formula.
        const H::ExprPtr inner =
            H::mkForall({{"x", H::Sort::integer()}},
                        H::mkOp(H::Op::EQ, {H::mkIdent("x", H::Sort::integer()),
                                            H::mkInt(0)}));
        const H::ExprPtr e = H::mkOp(
            H::Op::AND, {inner, H::mkOp(H::Op::EQ, {H::mkIdent("x", H::Sort::integer()),
                                                    H::mkInt(1)})});
        const H::ExprPtr r = H::substituteIdents(e, xToY());
        std::vector<std::string> ns;
        namesOf(r, ns);
        VERIFY(ns.size() == 2);
        VERIFY(ns[0] == "x");   // the shadowed one, untouched
        VERIFY(ns[1] == "y");   // the free one, renamed
    }

    // ---- The sort table, and leaving alone what is not named. ---------------
    {
        // A name in the sort table takes its new sort from there: the frontends
        // rename to a step variable that was declared at the same sort, and one
        // that was declared at a different one is the caller's statement.
        std::unordered_map<std::string, H::Sort> sorts;
        sorts["x"] = H::Sort::integer();
        const H::ExprPtr r = H::substituteIdents(x, xToY(), sorts);
        VERIFY(r->name == "y");
        VERIFY(H::sameSort(r->sort, H::Sort::integer()));
    }
    {
        // A term mentioning nothing in the map comes back as the SAME node, not
        // a copy. Cheap, and it means a caller can compare pointers to see
        // whether anything happened.
        const H::ExprPtr e = H::mkOp(H::Op::BV_ADD, {H::mkIdent("a", bv8),
                                                    H::mkIdent("b", bv8)});
        VERIFY(H::substituteIdents(e, xToY()) == e);
    }
    {
        VERIFY(H::substituteIdents(nullptr, xToY()) == nullptr);
    }

    std::cout << "All substituteIdents tests passed." << std::endl;
    return 0;
}
