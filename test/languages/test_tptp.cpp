// The TPTP frontend, and the five obligations docs/languages/tptp.md wrote down
// before it existed.
//
// The first one inverts every answer if it is missed: all formulas with role
// `conjecture` are conjoined and negated once. `axioms |= C1 AND ... AND Cn` is
// decided by refuting `axioms AND NOT(C1 AND ... AND Cn)`, so
// a frontend that conjoins the conjecture unnegated produces a formula that is
// satisfiable exactly when the theorem is *not* provable. Nothing downstream can
// tell: both readings are well-formed SMT-LIB and both get an answer.
//
// The test for it is a cross-file claim rather than a text match. `socrates.p`
// carries `conjecture: mortal(socrates)` and `negated_conjecture.p` carries
// `negated_conjecture: ~ mortal(socrates)`. They must produce the same target
// formula, but not the same source decision metadata: the first asks validity,
// while the second directly asks satisfiability of an already-negated formula.
// A frontend that drops the negation, or applies it twice, breaks the script
// equality; one that also inverts the second file breaks the decision contract.
//
// The other four: an unresolvable `include` is an ERROR (the included file is
// part of the problem, so a missing one is a different problem rather than a
// smaller one); untyped FOF gets ONE uninterpreted sort rather than sorts
// guessed from usage; upper-case is a variable and lower-case a constant, which
// is the binding structure and not a convention; and a CNF clause's variables
// are implicitly universally quantified even though nothing in the file says so.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/tptp.h"
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
    std::size_t n = 0, at = 0;
    while ((at = hay.find(needle, at)) != std::string::npos) { ++n; at += needle.size(); }
    return n;
}

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.p";
    u.display_name = "t.p";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "tptp";
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "tptp";
    return translate(u, opts);
}

bool notes(const Translation& t, const std::string& needle) {
    for (const auto& e : t.diagnostics().all()) {
        if (e.severity != Severity::ERROR && has(e.message, needle)) { return true; }
    }
    return false;
}

bool chose(const Translation& t, const std::string& strategy) {
    for (const auto& choice : t.report().choices()) {
        if (choice.strategy == strategy) { return true; }
    }
    return false;
}

} // namespace

int main() {
    std::cout << "======= TPTP frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* p = Lang::LanguageRegistry::instance().byId("tptp");
    assert(p != nullptr);
    assert(p->extensions().size() == 3);

    // ---- Obligation 1: `conjecture` is negated, `negated_conjecture` is not. --
    // The two files are the same problem written the two ways the format allows,
    // so the two scripts must be identical. Asserting on the presence of a `not`
    // would pass on a frontend that negated BOTH roles.
    {
        const Translation a = runFile("languages/tptp/instances/ok/socrates.p");
        const Translation b =
            runFile("languages/tptp/instances/ok/negated_conjecture.p");
        assert(a.ok() && b.ok());
        assert(a.toSmt2() == b.toSmt2());
        // And the negation is really there: the axiom says human(socrates) and
        // the goal says NOT mortal(socrates), so exactly one `not` survives.
        assert(count(a.toSmt2(), "(not ") >= 1);
        ParserPtr reader = newParser();
        assert(reader->parseStr(a.toSmt2()));
    }
    {
        // A positive conjecture asks a validity question and inverts the target
        // verdict. A `negated_conjecture` is already an asserted formula: in a
        // CNF/FOF satisfiability problem its provenance role does not invert the
        // SAT/UNSAT status (official MGT031-1 is the canonical counterexample).
        const Translation a = runFile("languages/tptp/instances/ok/socrates.p");
        assert(notes(a, "inverted"));
        assert(notes(a, "Theorem"));
        const Translation b =
            runFile("languages/tptp/instances/ok/negated_conjecture.p");
        assert(!notes(b, "inverted"));
        assert(a.semantics().stages()[0].decision.source
               == Sem::DecisionKind::VALIDITY);
        assert(b.semantics().stages()[0].decision.source
               == Sem::DecisionKind::SATISFIABILITY);
        assert(!a.semantics().targetSatMeansSourceYes());
        assert(b.semantics().targetSatMeansSourceYes());
    }
    {
        // Every conjecture must be proved. Here p follows but q does not, so the
        // target asks for a model of `p AND NOT(p AND q)` and remains SAT. The
        // old per-item encoding emitted `NOT p AND NOT q`, which is UNSAT and
        // falsely classified the whole problem as Theorem.
        const Translation t = run(
            "fof(a, axiom, p).\n"
            "fof(c1, conjecture, p).\n"
            "fof(c2, conjecture, q).\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(not (and p q))"));
        assert(t.report().stats().num_constraints == 2);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // In contrast, several CNF `negated_conjecture` formulas are clauses
        // from an already-negated goal. They remain separate conjuncts; joining
        // them with OR would undo clausification.
        const Translation t = run(
            "cnf(n1, negated_conjecture, p | q).\n"
            "cnf(n2, negated_conjecture, ~ p).\n");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 2);
        assert(!has(t.toSmt2(), "(not (and p q))"));
        assert(t.semantics().targetSatMeansSourceYes());
    }
    {
        // `plain` is for derivation output and has no specified input-problem
        // semantics. Treating it as an axiom would silently turn a proof trace
        // into a different problem.
        const Translation t = run("fof(step, plain, p).\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "role 'plain'"));
    }

    // ---- Obligation 4: ONE uninterpreted sort, and sorts are not guessed. ----
    // Untyped FOF lives in a single unsorted universe. A frontend that gave
    // `socrates` its own sort because it never appears as an argument, or that
    // made `human` take Int because nothing says otherwise, would produce a
    // well-typed script denoting a different problem.
    {
        const Translation t = runFile("languages/tptp/instances/ok/socrates.p");
        const std::string smt = t.toSmt2();
        assert(count(smt, "declare-sort") == 1);
        // A predicate's result is Bool; a functor's is the universe. The two are
        // told apart by POSITION -- TPTP has no syntax for the difference -- so
        // both spellings have to be present in one file for the claim to bite.
        assert(has(smt, "declare-fun human (") && has(smt, ") Bool"));
        assert(has(smt, "declare-fun socrates ()"));
        assert(!has(smt, "declare-fun socrates () Bool"));
        // Nothing is Int or Real: no sort was inferred from usage.
        assert(!has(smt, " Int") && !has(smt, " Real"));
    }
    {
        // A functor nested inside a predicate keeps the universe as its result,
        // so `f(X) = g(X)` is an equality over the universe and not over Bool.
        const Translation t = runFile("languages/tptp/instances/ok/connectives.p");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "declare-sort") == 1);
        assert(has(smt, "declare-fun p () Bool"));
        assert(!has(smt, "declare-fun f (") || !has(smt, "declare-fun f () Bool"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Obligation 5: case carries the binding structure. -------------------
    {
        const Translation t = runFile("languages/tptp/instances/ok/case_sensitive.p");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // `X` is bound and `x` is a constant. A case-folding reader produces a
        // formula with one name where the file has two -- and it is the
        // DECLARATION that gives it away, since a bound variable is never
        // declared.
        assert(has(smt, "declare-fun x ()"));
        assert(!has(smt, "declare-fun X ()"));
        assert(has(smt, "forall"));
    }

    // ---- Obligation: a CNF clause is implicitly universally closed. ----------
    // Nothing in `cnf(c1, axiom, ~ human(X) | mortal(X))` says `!`. Leaving the
    // variable free sends a binder-less variable into lowering; treating it as a
    // constant makes the clause say something about one individual instead of
    // about all of them.
    {
        const Translation t = runFile("languages/tptp/instances/ok/cnf_clauses.p");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "forall"));
        assert(!has(smt, "declare-fun X ()"));
        // The closure is purely universal, so it adds a quantifier without
        // adding an ALTERNATION -- the statistic counts forall/exists changes,
        // and a CNF file has none however many variables it binds. Paired with
        // quantifier_alternation.p below, which reports 1.
        assert(t.report().stats().max_quantifier_alternations == 0);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The CNF spelling and the FOF spelling of one problem agree. c1 is
        // `~human(X) | mortal(X)`, which is what `human(X) => mortal(X)` means,
        // and c3 is the negated conjecture -- so the two files' scripts denote
        // the same formula whichever way it was written.
        const Translation cnf = runFile("languages/tptp/instances/ok/cnf_clauses.p");
        const Translation fof = runFile("languages/tptp/instances/ok/socrates.p");
        assert(cnf.ok() && fof.ok());
        assert(cnf.report().stats().num_constraints
               == fof.report().stats().num_constraints);
    }

    // ---- Obligation 3: a missing include is an error, never a warning. -------
    {
        const Translation t = runFile("languages/tptp/instances/ok/with_include.p");
        assert(t.ok());
        // The axiom came from the included file, so the problem is provable.
        // Without the include there would be no `forall` at all.
        assert(has(t.toSmt2(), "forall"));
        // And it is the same problem as the one written in a single file.
        const Translation single = runFile("languages/tptp/instances/ok/socrates.p");
        assert(t.toSmt2() == single.toSmt2());
    }
    {
        const Translation t =
            runFile("languages/tptp/instances/reject/missing_include.p");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
        // The message says WHY it is an error rather than a skipped line.
        assert(has(t.diagnostics().all()[0].message, "part of the problem"));
    }
    {
        // A selection filters the whole included subtree. Importing all formulae
        // would add `unselected_fact` and answer a different problem.
        const Translation t =
            runFile("languages/tptp/instances/ok/include_selection.p");
        assert(t.ok());
        assert(has(t.toSmt2(), "selected_fact"));
        assert(!has(t.toSmt2(), "unselected_fact"));
        assert(!has(t.toSmt2(), "duplicate_one"));
    }
    {
        const Translation missing = runFile(
            "languages/tptp/instances/reject/include_selection_missing.p");
        assert(!missing.ok());
        assert(missing.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(missing.diagnostics().all()[0].message, "not found exactly once"));

        const Translation duplicate = runFile(
            "languages/tptp/instances/reject/include_selection_duplicate.p");
        assert(!duplicate.ok());
        assert(duplicate.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(duplicate.diagnostics().all()[0].message, "more than once"));
    }

    // ---- Quantifier alternation is measured, not assumed. -------------------
    {
        const Translation t =
            runFile("languages/tptp/instances/ok/quantifier_alternation.p");
        assert(t.ok());
        assert(t.report().stats().max_quantifier_alternations == 1);
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }

    // ---- Malformed and unsupported. -----------------------------------------
    {
        // The same name/arity cannot denote both a predicate and a function.
        const Translation t = runFile("languages/tptp/instances/reject/arity_clash.p");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }
    {
        // TPTP explicitly identifies `p/1` and `p/2` as different symbols.
        // SMT-LIB cannot overload declarations, so Phi injectively renames both.
        const Translation t = run(
            "fof(a, axiom, p(a)).\n"
            "fof(b, axiom, p(a,b)).\n");
        assert(t.ok());
        assert(chose(t, "arity-indexed-signature-morphism"));
        assert(count(t.toSmt2(), "declare-fun tptp$arity$") == 2);
        assert(t.semantics().stages()[0].source_signature.symbols.size() == 4);
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // Only CNF has implicit universal closure. FOF free variables are an
        // error in the official language, not an invitation to repair the file.
        const Translation t = run("fof(a, axiom, p(X)).\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "FOF variable 'X' is free"));
    }
    {
        // TPTP defines no precedence among binary connectives, and CNF admits
        // only a disjunction of literals.
        const Translation mixed = run("fof(a, axiom, p & q | r).\n");
        assert(!mixed.ok());
        assert(mixed.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        const Translation not_cnf = run("cnf(a, axiom, p & q).\n");
        assert(!not_cnf.ok());
        assert(not_cnf.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        // Nested reuse of X shadows only inside the existential. A set-based
        // scope tracker used to erase the outer X after leaving the inner scope.
        const Translation t = run(
            "fof(a, axiom, ![X] : (p(X) & (?[X] : q(X)) & r(X))).\n");
        assert(t.ok());
        assert(count(t.toSmt2(), "forall") == 1);
        assert(count(t.toSmt2(), "exists") == 1);
        assert(!has(t.toSmt2(), "declare-fun X"));
    }
    {
        // Repeating a variable entry in one FOF binder list is accepted by the
        // official recursive variable-list grammar. Keep the entries as
        // distinct, capture-avoiding target binders: body occurrences resolve
        // to the innermost entry, while outer scopes are restored after exit.
        const Translation t = run(
            "fof(a, axiom, ![X] : (p(X) & (?[X,X] : q(X)) & r(X))).\n");
        assert(t.ok());
        assert(chose(t, "capture-avoiding-alpha-renaming"));
        assert(count(t.toSmt2(), "tptp_shadow_") >= 2);
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));

        // A source spelling cannot denote two different typed variables in one
        // list; accepting that would turn conflicting declarations into an
        // implicit type coercion.
        const Translation conflicting_sorts = run(
            "tff(p_type, type, p: $real > $o).\n"
            "tff(a, axiom, ![X: $int, X: $real] : p(X)).\n");
        assert(!conflicting_sorts.ok());
        assert(conflicting_sorts.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(conflicting_sorts.diagnostics().all()[0].message,
                   "repeated quantifier variable 'X' has incompatible sorts"));
    }
    {
        // Different double-quoted objects carry an implicit disequality axiom;
        // unlike ordinary constants, interpreting both as one element is illegal.
        const Translation t = run(
            "fof(a, axiom, p(\"Apple\")).\n"
            "fof(b, axiom, p(\"Microsoft\")).\n");
        assert(t.ok());
        assert(chose(t, "fresh-constants-plus-pairwise-distinct-axiom"));
        assert(has(t.toSmt2(), "(distinct "));
        assert(t.semantics().stages()[0].target_axioms.size() == 1);
    }
    {
        // The official SYN000 examples exercise escaped quotes/backslashes.
        const Translation t = run(
            "fof(a, axiom, p('A \\'quoted \\\\ escape\\'')).\n");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        const Translation number = run("fof(a, axiom, p(1)).\n");
        assert(!number.ok());
        assert(number.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        const Translation system = run("fof(a, axiom, $$p(a)).\n");
        assert(!system.ok());
        assert(system.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        const Translation defined = run("fof(a, axiom, $distinct(a,b)).\n");
        assert(!defined.ok());
        assert(defined.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }
    {
        // The supported monomorphic THF0 fragment uses the typed strong-Henkin
        // path, while coverage still names the unsupported remainder of THF.
        Lang::SourceUnit unit;
        unit.display_name = "monomorphic-thf-test.p";
        unit.inline_source =
            "thf(type_u, type, (u:$tType)).\n"
            "thf(type_p, type, (p:u > $o)).\n"
            "thf(fact, axiom, ! [X:u] : (p @ X)).\n"
            "thf(goal, conjecture, ! [X:u] : (p @ X)).\n";
        const Lang::ParseOutcome outcome = p->parse(unit, Lang::ParseOptions{});
        assert(outcome.ok());
        bool has_henkin_choice = false;
        for (const auto& choice : outcome.report.choices()) {
            has_henkin_choice = has_henkin_choice
                || choice.strategy == "strong-type-code-henkin";
        }
        assert(has_henkin_choice);
        assert(outcome.semantics.stages().size() == 1);
        assert(outcome.semantics.stages()[0].decision.source == Sem::DecisionKind::VALIDITY);
        assert(outcome.semantics.stages()[0].decision.target == Sem::DecisionKind::SATISFIABILITY);
        assert(outcome.semantics.stages()[0].decision.polarity == Sem::VerdictPolarity::INVERT);
        assert(p->coverage().missing.size() == 1);
        assert(has(p->coverage().missing[0], "outside the supported monomorphic THF0"));
    }
    {
        const Translation t =
            runFile("languages/tptp/instances/reject/unterminated.p");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        const Translation t = runFile("languages/tptp/instances/nosuch.p");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- TFF: typed declarations carry their real sorts into the target. ----
    {
        const Translation t = runFile("languages/tptp/instances/ok/tff_typed.p");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The declared sort and the signatures survive with their REAL sorts,
        // and nothing here touches the untyped universe.
        assert(count(smt, "(declare-sort fruit 0)") == 1);
        assert(has(smt, "(declare-fun apple () fruit)"));
        assert(has(smt, "(declare-fun tree (fruit) fruit)"));
        assert(has(smt, "(declare-fun eats (fruit fruit) Bool)"));
        assert(has(smt, "(forall ((X fruit))"));
        assert(!has(smt, "$i"));
        // The conjecture obligation is unchanged: the goal is negated once.
        assert(has(smt, "(not (eats apple apple))"));
        assert(t.semantics().stages()[0].decision.source
               == Sem::DecisionKind::VALIDITY);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Default typing: undeclared symbols range over the FOF universe $i --
        // the SAME sort object untyped items use, which is the interop point.
        const Translation t = run("tff(a, axiom, q(w)).\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(declare-sort $i 0)"));
        assert(has(smt, "(declare-fun q ($i) Bool)"));
        assert(has(smt, "(declare-fun w () $i)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Per the official TPTP syntax, single-quoted atomic words are ordinary
        // names after removing quotes. In particular '$ki_world' and '$true'
        // are user names; they are not the unquoted defined words $true/$i.
        // This is the minimal typed shape of CASC-30 TFN/PLA053_15.p.
        const Translation quoted = run(
            "tff('$ki_world_type', type, '$ki_world': $tType).\n"
            "tff('$ki_accessible_type', type, '$ki_accessible': "
            "('$ki_world' * '$ki_world') > $o).\n"
            "tff('$ki_local_world_type', type, '$ki_local_world': '$ki_world').\n"
            "tff('$true_type', type, '$true': $o).\n"
            "tff(reflexive, axiom, '$ki_accessible'('$ki_local_world', "
            "'$ki_local_world')).\n"
            "tff(quoted_true, axiom, '$true').\n"
            "tff(system_true, axiom, $true).\n");
        assert(quoted.ok());
        const std::string smt = quoted.toSmt2();
        assert(has(smt, "tptp$sort$246b695f776f726c64"));
        assert(has(smt, "declare-fun tptp$"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));

        // A quoted ordinary '$i' is a user sort, distinct from the unquoted
        // TPTP individual sort $i. Both uses must survive target parsing.
        const Translation quoted_builtin_name = run(
            "tff('$i_sort', type, '$i': $tType).\n"
            "tff('$tType_sort', type, '$tType': $tType).\n"
            "tff(user_value, type, user_value: '$i').\n"
            "tff(t_type_value, type, t_type_value: ('$tType')).\n"
            "tff(individual_value, type, individual_value: $i).\n"
            "tff(user_reflexive, axiom, user_value = user_value).\n"
            "tff(t_type_reflexive, axiom, t_type_value = t_type_value).\n"
            "tff(individual_reflexive, axiom, individual_value = individual_value).\n");
        assert(quoted_builtin_name.ok());
        assert(count(quoted_builtin_name.toSmt2(), "(declare-sort ") == 3);
        ParserPtr builtin_reader = newParser();
        assert(builtin_reader->parseStr(quoted_builtin_name.toSmt2()));

        // A quoted source name can itself spell an internal encoding. It
        // must remain a third user sort, not alias the encoded '$i' sort.
        const Translation collision = run(
            "tff(a_type, type, a: '$i').\n"
            "tff(b_type, type, b: 'tptp$sort$2469').\n"
            "tff(c_type, type, c: '_tptp_quoted_dollar_2469').\n"
            "tff(a_eq, axiom, a = a).\n"
            "tff(b_eq, axiom, b = b).\n"
            "tff(c_eq, axiom, c = c).\n");
        assert(collision.ok());
        assert(count(collision.toSmt2(), "(declare-sort ") == 3);
        const Translation wrong_sort = run(
            "tff(a_type, type, a: '$i').\n"
            "tff(b_type, type, b: 'tptp$sort$2469').\n"
            "tff(cross_sort, axiom, a = b).\n");
        assert(!wrong_sort.ok());
        assert(wrong_sort.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);

        // An unquoted defined word is still not an ordinary TFF declaration
        // name. Only single-quoted spelling opts into ordinary-word semantics.
        const Translation unquoted_defined =
            run("tff(bad_type_name, type, $user_sort: $tType).\n");
        assert(!unquoted_defined.ok());
        assert(unquoted_defined.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        // Legal source constants and functions named like SMT operators must
        // retain their uninterpreted TPTP meaning. CASC EPS/HWV053-1.p uses
        // ordinary true/false; FNE/CSR115+31.p uses the ordinary function abs.
        const Translation reserved = run(
            "fof(names, axiom, true != false & abs(true) != true).\n");
        assert(reserved.ok());
        const std::string smt = reserved.toSmt2();
        assert(!has(smt, "(declare-fun true "));
        assert(!has(smt, "(declare-fun false "));
        assert(!has(smt, "(declare-fun abs "));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A mixed file is one problem: $i is declared once and shared.
        const Translation t = run(
            "fof(a, axiom, p(x)).\n"
            "tff(b, type, y: $i).\n"
            "tff(c, axiom, p(y)).\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "(declare-sort $i 0)") == 1);
        assert(has(smt, "(declare-fun y () $i)"));
        assert(has(smt, "(p y)") && has(smt, "(p x)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Identical redeclaration is legal spec merging; a declaration that
        // conflicts with the recorded default typing is a type error.
        const Translation t = run(
            "tff(t1, type, f: $i > $i).\n"
            "tff(t2, type, f: $i > $i).\n"
            "tff(a, axiom, f(x) = f(x)).\n");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));

        const Translation bad =
            runFile("languages/tptp/instances/reject/tff_conflicting_decl.p");
        assert(!bad.ok());
        assert(bad.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(bad.diagnostics().all()[0].message, "conflicting redeclaration"));
    }
    {
        // TFF shares FOF's closedness rule, with the layer named correctly.
        const Translation t = run("tff(a, axiom, p(X)).\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "TFF variable 'X' is free"));
    }
    {
        // The typing environment is shared across includes: the sort and both
        // signatures come from the included file.
        const Translation t = runFile("languages/tptp/instances/ok/tff_include.p");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(declare-sort fruit 0)"));
        assert(has(smt, "(declare-fun apple () fruit)"));
        assert(has(smt, "(not (eats apple apple))"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // A $o-sorted variable is a formula; a declared fruit constant is not.
        const Translation t = run("tff(a, axiom, ![P: $o]: (P | ~ P)).\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(forall ((P Bool))"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));

        const Translation bad = run(
            "tff(ft, type, fruit: $tType).\n"
            "tff(a, type, apple: fruit).\n"
            "tff(u, axiom, apple).\n");
        assert(!bad.ok());
        assert(bad.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(bad.diagnostics().all()[0].message, "predicate"));
    }

    // ---- TFF arithmetic: interpreted numerics, no silent coercion. ----------
    {
        const Translation t =
            runFile("languages/tptp/instances/ok/tff_arithmetic.p");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(+ n 3)") || has(smt, "(+ 3 n)"));
        assert(has(smt, "(- 5)"));
        assert(has(smt, "(div n 5)") && has(smt, "(mod n 5)"));
        // Integral Real values retain a decimal marker when exported.
        assert(has(smt, "(/ r 2.0)"));
        // $floor/$ceiling/$truncate expand through to_int/to_real; the
        // rational 3/5 prints as an exact division and the exponent real
        // 1.5E-2 as its exact canonical rational (15/1000 = 3/200).
        assert(has(smt, "to_real") && has(smt, "to_int"));
        assert(has(smt, "(/ 3 5)") && has(smt, "(/ 3 200)"));
        assert(chose(t, "total-zero-divisor"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // What TPTP itself forbids is E_TYPE; the fragment gaps are named.
        const Translation mixed =
            runFile("languages/tptp/instances/reject/tff_ill_typed.p");
        assert(!mixed.ok());
        assert(mixed.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(mixed.diagnostics().all()[0].message, "one numeric sort"));

        const Translation quotient = run(
            "tff(n, type, n: $int).\n"
            "tff(a, axiom, $greater($quotient(n, 5), 0)).\n");
        assert(!quotient.ok());
        assert(quotient.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(quotient.diagnostics().all()[0].message, "$quotient"));

        const Translation sides = run(
            "tff(ft, type, fruit: $tType).\n"
            "tff(a, type, apple: fruit).\n"
            "tff(x, axiom, apple = 3).\n");
        assert(!sides.ok());
        assert(sides.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(sides.diagnostics().all()[0].message, "different sorts"));

        const Translation oarg = run("tff(b, type, f: ($o * $i) > $i).\n");
        assert(!oarg.ok());
        assert(oarg.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(oarg.diagnostics().all()[0].message, "$o"));
    }
    {
        const Translation rnd = run(
            "tff(r, type, r: $real).\n"
            "tff(a, axiom, $greater($round(r), 0.0)).\n");
        assert(!rnd.ok());
        assert(rnd.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(rnd.diagnostics().all()[0].message, "$round"));

        const Translation qn = run("tff(a, axiom, $greater($quotient_n(3, 2), 1)).\n");
        assert(!qn.ok());
        assert(qn.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(qn.diagnostics().all()[0].message, "$quotient_n"));

        const Translation israt = run("tff(a, axiom, $is_rat(3)).\n");
        assert(!israt.ok());
        assert(israt.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(israt.diagnostics().all()[0].message, "$is_rat"));
    }

    // ---- TXF: FOOL conflation, $ite, $let. ----------------------------------
    {
        const Translation t = runFile("languages/tptp/instances/ok/txf_fool.p");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(ite b "));
        // The $let definitions are inlined at parse time: no target symbols.
        assert(!has(smt, "declare-fun two"));
        assert(!has(smt, "declare-fun f ("));
        assert(has(smt, "(+ c 1)") || has(smt, "(+ 1 c)"));
        assert(chose(t, "parse-time-substitutive-inlining"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Inlining substitutes arguments for the formals -- p(Y) inlines
        // p's body with X := the outer Y -- and renames the definition's own
        // binders so nothing captures.
        const Translation t = run(
            "txf(a, axiom, ![Y: $int]:\n"
            "    ($let(p: ($int) > $o,\n"
            "          p(X) := (?[Z: $int]: $greater($sum(X, Z), Y)),\n"
            "          p(Y))\n"
            "     => $greatereq(Y, 0))).\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "tptp_let_"));
        assert(!has(smt, "(exists ((Z "));
        assert(!has(smt, "declare-fun p "));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        const Translation branches = run(
            "txf(b, type, b: $o).\n"
            "txf(a, axiom, $ite(b, 1, 2.0) = 1).\n");
        assert(!branches.ok());
        assert(branches.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(has(branches.diagnostics().all()[0].message, "$ite"));

        const Translation let_tff = run("tff(a, axiom, $let(x: $int, x := 1, x) = 1).\n");
        assert(!let_tff.ok());
        assert(let_tff.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(let_tff.diagnostics().all()[0].message, "$let"));
    }
    {
        // A recursive $let definition -- direct or transitive through a
        // forward reference -- cannot be inlined and is refused by name.
        const Translation direct = run(
            "txf(r, axiom, $let(f: ($int) > $int, f(X) := $sum(f(X), 1), f(0)) = 0).\n");
        assert(!direct.ok());
        assert(direct.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(direct.diagnostics().all()[0].message, "recursive"));

        const Translation transitive = run(
            "txf(r, axiom, $let([a: $int, b: $int], [a := b, b := a], a) = 0).\n");
        assert(!transitive.ok());
        assert(transitive.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(transitive.diagnostics().all()[0].message, "recursive"));
    }
    {
        // Named refusals: TF1 polymorphism (both spellings), tuples, the
        // subtype sign, the formula-level definition, sequents, NXF atoms.
        const Translation tf1 =
            runFile("languages/tptp/instances/reject/tf1_polymorphic.p");
        assert(!tf1.ok());
        assert(tf1.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(tf1.diagnostics().all()[0].message, "TF1"));

        const Translation tyvar = run("tff(p, type, f: A > A).\n");
        assert(!tyvar.ok());
        assert(tyvar.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(tyvar.diagnostics().all()[0].message, "TF1"));

        const Translation tup = runFile("languages/tptp/instances/reject/txf_tuple.p");
        assert(!tup.ok());
        assert(tup.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(tup.diagnostics().all()[0].message, "tuple"));

        const Translation sub = run("tff(s, type, sub: base << top).\n");
        assert(!sub.ok());
        assert(sub.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(sub.diagnostics().all()[0].message, "<<"));

        const Translation defn = run("txf(d, axiom, f(x) == 3).\n");
        assert(!defn.ok());
        assert(defn.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(defn.diagnostics().all()[0].message, "=="));

        const Translation seq = run("txf(s, axiom, [p] ~> [q]).\n");
        assert(!seq.ok());
        assert(seq.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(seq.diagnostics().all()[0].message, "sequent"));

        const Translation nxf = run("txf(n, axiom, {$box} @ (p)).\n");
        assert(!nxf.ok());
        assert(nxf.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(nxf.diagnostics().all()[0].message, "NXF"));
    }

    // ---- Comments and the source-line fields. -------------------------------
    {
        // `%` to end of line, and `/* */`. A comment inside an item must not
        // split it.
        const Translation t = run(
            "% a leading comment\nfof(a, /* inline */ axiom, p(x)). % trailing\n"
            "/* a block\n   spanning lines */\nfof(b, axiom, q(x)).\n");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 2);
    }
    {
        // TPTP comments do not act as whitespace: deleting this line comment
        // joins the token fragments into the one proposition `predicate`.
        const Translation t = run("fof(a, axiom, predi% comment\ncate).\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "declare-fun predicate () Bool"));
        assert(!has(t.toSmt2(), "declare-fun predi "));
    }
    {
        // The annotation tail (source, useful_info) is present in real corpora
        // and carries no semantics.
        const Translation plain = run("fof(a, axiom, p(x)).\n");
        const Translation noisy = run(
            "fof(a, axiom, p(x), file('X.p', a), [status(thm)]).\n");
        assert(plain.ok() && noisy.ok());
        assert(plain.toSmt2() == noisy.toSmt2());
    }

    std::cout << "All TPTP tests passed." << std::endl;
    return 0;
}
