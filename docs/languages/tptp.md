# TPTP CNF/FOF/TFF/TXF to SMT: Semantic Construction

## 1. Supported object logic

The frontend implements the classical `cnf` and `fof` layers of the TPTP
language, the typed `tff`/`txf` dialects (TFF0 arithmetic included; TF1
polymorphism excluded), and a monomorphic THF0 Boolean/individual fragment. It
does not reinterpret the whole TPTP family as one logic:

| Layer | Status | Reason |
|---|---|---|
| CNF | exact on accepted fragment | first-order clauses with implicit universal closure |
| FOF | exact on accepted fragment | classical first-order logic with equality |
| TFF | exact on accepted fragment | monomorphic typed first-order logic; typed declarations, interpreted arithmetic |
| TXF | exact on accepted fragment | TFF plus the FOOL conflation, `$ite`, and `$let` (inlined at parse time) |
| THF0 monomorphic fragment | exact on accepted fragment | typed Boolean/individual terms, arrows, lambda, application, quantification, equality, recursive selected includes, and the strong Henkin encoding |
| Remaining THF, DHF/NXF/NHF | refused | include namespaces, polymorphism, interpreted arithmetic, quoted expression atoms, and unsupported syntax are outside the implemented fragment |

THF includes resolve relative to the containing file, the working directory,
or the `TPTP` root. A formula-name selection filters the complete recursively
included subtree; missing or duplicate selected names are errors. Type
declarations and formulas retain their original file/line/column locations,
and included declarations share one two-pass signature. Include-only wrappers
dispatch according to their selected contents. This implements the
[TPTP include semantics](https://tptp.org/UserDocs/ProblemLibraryManual/TPTPTR.shtml);
mixed selected THF and first-order statements and include namespaces remain
unsupported.

Repeated THF declarations contribute one signature entry when their parsed types
agree, including declarations reached through overlapping includes. Conflicting
types and reuse of a type name as a term symbol are rejected at the conflicting
declaration. This follows the [TPTP type-declaration rule](https://tptp.org/UserDocs/ProblemLibraryManual/TPTPTR.shtml).

THF application operands include prefix Boolean formulas and quantified formulas.
Lambda and quantifier bodies respect the unit-formula boundary: an outer `@`
does not enter a lambda body through an unparenthesized negation. Parentheses
extend that body's scope, following the [official THF grammar](https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html).

Parenthesized Boolean connective terms `(~)`, `(&)`, `(|)`, `(~&)`, `(~|)`,
`(=>)`, `(<=)`, `(<=>)`, and `(<~>)` can be passed as function values or
applied with `@`. They become typed, curried Boolean lambdas with fresh
binders, preserving the connective's truth table. Infix NAND and NOR are
also accepted in this fragment.

Unquoted system symbols beginning `$$` are also refused because TPTP deliberately gives
them tool-specific semantics. Unsupported defined symbols, numeric terms in an
untyped formula, formula roles without input-problem semantics, and include
namespaces are rejected rather than treated as uninterpreted syntax. Inside the
typed dialects, legal-but-unread constructs are refused by name: TF1
polymorphic types (`!>` quantified types and type variables in signatures),
tuples and tuple types, `<tff_subtype>` (`<<`), the formula-level
`<txf_definition>` (`==`), `<txf_sequent>`, NXF `@` atoms, and the
round-to-nearest operators `$quotient_n`, `$remainder_n`, `$round` (whose
tie-break TPTP does not pin down), plus `$is_rat` (not expressible over SMT
Reals, where `$rat` and `$real` share one carrier).

The implementation is pinned to the current TPTP 9.3 grammar family. The online
BNF identifies itself as 9.3.0.4; the official syntax-test problem pages used in
the audit identify themselves as 9.3.1.

<!-- implicit-constraints:
  every free variable in a CNF clause => universally quantified over the complete clause; FOF free variables are malformed rather than implicitly closed
  the untyped individual sort => a nonempty carrier, as required by classical first-order TPTP models
  equal double-quoted distinct objects => forbidden; A_Sigma must add pairwise target distinctness, while ordinary constants need not be distinct from them
  the same atomic spelling at different arities => different source signature symbols; Phi must rename injectively instead of rejecting legal overloading or merging interpretations
  one or more positive `conjecture` formulae => a validity question lowered as axioms AND NOT(AND conjectures), with SAT/UNSAT decision polarity inverted
  `negated_conjecture` without a positive conjecture => an already-negated asserted sentence in a direct satisfiability question; its role does not invert SAT/UNSAT
  include(file,[names]) => selects named formulae from the complete recursively included subtree; a missing or duplicate selected name is an error
  TFF `$i` => the same uninterpreted sort the untyped path introduces, so a mixed FOF/TFF file is one problem
  undeclared TFF symbol => default typing ($i * ... * $i) > $i / > $o by position, recorded as an assumption; a conflicting later declaration is a type error, an identical one legal spec merging
  TFF arithmetic operators => ad-hoc polymorphic over ONE numeric sort per application; TPTP has no implicit $int-to-$real coercion, so mixed arguments are what TPTP itself forbids (a type error, not a fragment gap)
  TPTP division/remainder => total; a zero divisor yields an unspecified value, exactly SMT-LIB's reading, so no definedness guard is added
  TXF `$let` => parse-time inlining with capture-avoiding renaming; a (transitively) recursive definition cannot be inlined and is refused by name
-->

## 2. Source institution

For a parsed problem, the optimization-aware institution is

\[
\mathcal I_{\mathrm{TPTP}}=(\mathbf{Sign},\operatorname{Sen},
\operatorname{Mod},\models,\operatorname{Cost},\preceq,
\operatorname{Obs}).
\]

- **Sign.** One nonempty individual carrier `U`; total function and relation
  symbols identified by atomic spelling and arity; interpreted equality. Under
  TFF/TXF, additionally the declared user sorts, the interpreted sorts
  `$int`/`$rat`/`$real`, and `$o`; a signature is then a typing
  `f : (S1 * ... * Sn) > R` with `R = $o` exactly for predicates, and TPTP's
  default typing `($i * ... * $i) > $i` / `> $o` for undeclared symbols.
- **Sen.** Closed FOF formulae, CNF clauses whose free variables are
  implicitly universally quantified, and well-typed TFF/TXF formulae, paired
  with TPTP roles. `type` items contribute to the signature and carry no
  sentence.
- **Mod.** A nonempty `U`, total interpretations of every function/relation,
  and fixed interpretations of distinct objects; under the typed dialects,
  carriers per sort (the numerics interpreted as the integers and the reals)
  and total interpretations respecting the declared typings.
- **Satisfaction.** Ordinary classical first-order satisfaction with equality;
  equality is ad-hoc polymorphic over one shared sort per equation.
- **Cost/order.** No objective; satisfaction order is vacuous.
- **Observables.** Interpretations of the source functions and relations.

The assumption profile is therefore: nonempty possibly finite/infinite carrier,
total functions, no undefined values, native quantifiers, and strategy-only
annotations; the untyped layers add one untyped universe, while TFF/TXF add
declared sorts, interpreted arithmetic with total division, and the TXF term/
formula conflation.

## 3. Two different source questions

The role `conjecture` changes the decision problem. For axiom-like formulae
`A` and positive conjectures `C1,...,Cn`, the source asks

\[
A\models C_1\land\cdots\land C_n.
\]

The target refutation is

\[
A\land\neg(C_1\land\cdots\land C_n).
\]

Thus target `UNSAT` is a positive validity result (`Theorem`) and target `SAT`
is a countermodel (`CounterSatisfiable`). Multiple conjectures are negated once
as a conjunction; negating each independently asks a different question.

By contrast, `negated_conjecture` is an already-negated formula, commonly one
of several clausified clauses. If a file has no positive `conjecture`, its source
question remains satisfiability of all asserted formulae. SAT/UNSAT polarity is
preserved. Official `MGT031-1` is labelled `Satisfiable` despite containing
`negated_conjecture`; treating the role alone as a validity request is wrong.

## 4. Translation construction

The executable adapter is

\[
\mathcal T=(\Phi,A_\Sigma,\alpha,\beta,h).
\]

### Signature morphism `Phi`

- The untyped carrier maps to one SMT uninterpreted sort `$i`. TFF/TXF `$i`
  denotes the SAME sort, so a mixed FOF/TFF file is one problem.
- Every argument and ordinary function result maps to `$i`; predicate results
  map to `Bool`.
- TPTP permits the same spelling at different arities, while SMT-LIB does not
  permit user-symbol overloading. Such identities are injectively renamed.
- Quoted spellings that are not stable SMT simple symbols, and ordinary names
  that collide with SMT builtins (such as `true`, `false`, or `abs`), receive
  an injective ASCII name. The inverse is retained in the contract.
- A single-quoted dollar word is an ordinary name: `'$true'` is distinct from
  `$true`, and the user sort `'$i'` is distinct from the builtin individual sort.
  Sort encoding also handles source names that resemble generated names, so
  quoting an encoding prefix cannot accidentally merge two source sorts.
- A spelling used at the same arity as both function and predicate is rejected.
- Under TFF/TXF, declared signatures map sort-wise: user sorts to injectively
  named uninterpreted sorts, `$o` to `Bool`, `$int` to `Int`, and `$rat`/`$real` to
  `Real`. Argument sorts cannot be `$o`; a conflicting redeclaration -- against
  either an earlier declaration or a recorded default typing -- is a type
  error, while an identical redeclaration is legal spec merging.

The source signature uses a canonical identifier derived from the source
spelling and arity. `symbol_map` records each canonical source identity and its
actual SMT name, rather than pretending that renaming is identity.

### Added axioms `A_Sigma`

Different double-quoted distinct objects must denote different elements. They
become fresh `$i` constants plus one pairwise `distinct` axiom. No inequality is
added against ordinary constants, because TPTP does not require it in untyped
FOF.

### Sentence map `alpha`

- `&`, `|`, `~`, `=>`, `<=`, `<=>`, `<~>`, `~&`, and `~|` map to their exact
  Boolean definitions.
- Equality maps to SMT equality over the shared sort of its sides; a sort
  mismatch is what TPTP itself forbids, hence a type error rather than a
  coercion.
- Explicit FOF quantifiers map to native SMT quantifiers; TFF/TXF typed
  binders carry their declared sorts.
- CNF free variables receive one outer universal closure; FOF free variables
  are errors.
- Positive conjectures are combined and negated as described above.
- `negated_conjecture` and axiom-like roles are asserted as written.
- `include(file,[names])` filters the complete recursively included subtree;
  a missing or duplicate selected name is an error. The typing environment
  lives on the parser, so declarations cross the include boundary both ways.
- Numeric literals sort by form: `3` is $int, `3/5` is $rat, `3.5` and
  `1.5E-2` are $real (the exponent spelling expands to the exact rational, as
  SMT-LIB reals have no exponent form). The arithmetic builtins map to the
  corresponding theory operators: `$sum`/`$difference`/`$product`/`$uminus`,
  `$quotient` (real division; on $int it is what TPTP itself forbids),
  `$quotient_e/_t/_f` and `$remainder_e/_t/_f` to the Euclidean, truncating
  and flooring families, `$floor`/`$ceiling`/`$truncate` to their exact
  `to_int`/`to_real` definitions (identity on $int), `$to_int`/`$to_rat`/
  `$to_real` to the conversion operators (identity when already at the target
  sort), `$less`/`$lesseq`/`$greater`/`$greatereq` to the comparisons, and
  `$is_int` to `is_int` (literal `true` on an $int argument). Division and
  remainder are total -- a zero divisor is unspecified, exactly SMT-LIB's
  reading -- so no definedness guard is added; the choice is recorded.
- TXF adds `$ite` (branches must share one sort) and `$let`, the latter
  inlined at parse time with capture-avoiding renaming of the definition's
  binders; a direct or transitive self-reference would make inlining diverge
  and is refused by name. Under TXF a `$o`-sorted term is a formula and vice
  versa (FOOL), so the term parser accepts a parenthesized formula and the
  formula parser accepts any Bool-sorted term as an atom.

TPTP specifies no precedence between binary connectives. Mixed binary operators
must be parenthesized; the frontend does not invent an `&`-before-`|` rule. CNF
is parsed with its own disjunction-of-literals grammar rather than the FOF
grammar.

### Model map `beta` and objective map `h`

`beta` renames each target function/relation interpretation back to its
canonical source identity and removes no source symbol. Generated names and the
distinct-object axiom are target representation details. There is no objective,
so `h` is the identity on the singleton satisfaction order.

## 5. Correctness obligations

For direct satisfiability problems, the exactness claim is

\[
N\models A_\Sigma\land\alpha(\Gamma)
\quad\Longleftrightarrow\quad
\beta(N)\models\Gamma.
\]

Soundness follows because every SMT model decodes to the same total first-order
functions/relations and satisfies the distinct-object requirements.
Completeness follows by interpreting each injectively renamed target symbol as
its source interpretation; every source model extends to a target model.

For a positive conjecture, the sentence equivalence is instead the exact
refutation theorem

\[
A\models C
\quad\Longleftrightarrow\quad
A_\Sigma\land\alpha(A)\land\neg\alpha(C)\text{ is UNSAT}.
\]

This is exact but verdict-inverting; it is not an approximation.

## 6. Refusal policy

The frontend reports a hard diagnostic for:

- unresolved includes, missing/duplicate selected names, or include namespaces;
- free FOF variables, illegal CNF formula shape, and mixed unparenthesized binary
  connectives;
- same-name/same-arity function-predicate clashes;
- TFF/TXF type errors, which are what TPTP itself forbids: ill-sorted
  applications, equality across sorts, mixed-sort arithmetic (no implicit
  coercion), `$quotient` on $int, $o argument sorts, and conflicting
  (re)declarations;
- `plain`, `interpretation`, `logic`, `unknown`, and other roles without
  supported classical input-problem semantics (`type` is accepted in tff/txf
  items only);
- THF outside the monomorphic Boolean/individual THF0 fragment, and other
  higher-order, dependent, or non-classical layers;
- the named TFF/TXF fragment gaps: TF1 polymorphic types (`!>`, type variables,
  applied type constructors, `$tType` beyond a bare sort declaration), tuples
  and tuple types, `<tff_subtype>` (`<<`), `<txf_definition>` (`==`),
  `<txf_sequent>`, NXF `@` atoms, `$quotient_n`, `$remainder_n`, `$round`,
  `$is_rat`, and recursive `$let` definitions;
- system-specific `$$` symbols and unsupported interpreted `$` symbols.

Repeated names of the same sort in a quantifier list are alpha-renamed in
source order. Body occurrences refer to the innermost binding; enclosing scopes
are restored after the list. Conflicting sorts for a repeated name are rejected.
Symbol finalization preserves unchanged HIR nodes and memoizes shared nodes,
avoiding a second full copy of large CNF formula trees.

Source and useful-info annotation fields are parsed as item boundaries but do
not constrain models, matching their metadata role.

## 7. Verification record

Focused tests cover conjecture polarity, CNF closure, FOF closedness, arity
overloading, function/predicate clashes, lexical scope and alpha-renaming,
quoted identifiers, distinct objects, comment deletion, include filtering, and
explicit refusals. The TFF/TXF cases add: typed declarations with their real
sorts in the target, typed quantifiers, default typing and its conflicts,
identical redeclarations, the shared `$i` across a mixed FOF/TFF file, the
typing environment across includes, the arithmetic builtins (including one
`$quotient_e`/`$truncate`/`$floor` case and exact rational/exponent literals),
ill-typed arithmetic and equality as E_TYPE, `$ite` with branch-sort
agreement, `$let` inlining with capture-avoiding renaming (including a
predicate definition whose body quantifies), recursive-definition refusals,
and every named refusal listed in §6. Each accepted fixture's emitted script
is re-parsed.

Fixtures live in `languages/tptp/instances`: `ok/tff_typed.p`,
`ok/tff_arithmetic.p`, `ok/txf_fool.p`, `ok/tff_include.p` (with
`ok/Axioms/tff_typed.ax`), and `reject/tff_ill_typed.p`,
`reject/tff_conflicting_decl.p`, `reject/tf1_polymorphic.p`,
`reject/txf_tuple.p`.

External validation used official online files without vendoring them:

- `SYN000-1` and `SYN000+1` translated completely; Z3 returned `unsat` for both,
  matching `Unsatisfiable` and `Theorem` after the declared decision mapping.
- `SYN000-2` and `SYN000+2` parsed every supported construct before correctly
  refusing the official `unknown` role.
- Ten easy CNF/FOF problems listed by the official Quick Guide all translated
  after resolving one official axiom include. Z3 was conclusive on seven within
  20 seconds and all seven matched their SZS polarity; three timed out.

Run the local checks with:

```sh
cmake --build build --target test_tptp test_semantic_core test_semantic_contract_coverage
./build/test/test_tptp
./build/test/test_semantic_core
./build/test/test_semantic_contract_coverage
```

## 8. Primary references

- [TPTP language overview](https://tptp.org/UserDocs/TPTPLanguage/TPTPLanguage.shtml)
- [Current TPTP BNF](https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html)
- [Annotated formula roles](https://tptp.org/UserDocs/TPTPLanguage/AnnotatedFormulae.html)
- [Problem-library manual and include semantics](https://tptp.org/UserDocs/ProblemLibraryManual/TPTPTR.shtml)
- [Official parser test and known-result list](https://tptp.org/UserDocs/QuickGuide/)
- [SZS ontology](https://tptp.org/UserDocs/SZSOntology/)
