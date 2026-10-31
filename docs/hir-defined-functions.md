# Defined functions in HIR

`FunDecl` describes an ordinary uninterpreted function when `body` is null.
An auxiliary must be defined because its interpretation cannot be hidden
without a function-witness projection. An exact non-recursive definition
supplies a body and a same-arity list of
formal `binders`; binder sorts must match the existing `params` signature.
Body variables use `BOUND_VAR`, while free `IDENT` occurrences still resolve
against model declarations. Lowering assigns fresh SMT parameter names so a
bound variable can safely share a source spelling with a free global identifier.
Freshness treats quoted and bare SMT symbols as equivalent, including generated
aliases for reserved names.
HIR identifier checking compares complete declared and recorded sorts, including
bit-vector widths, array component sorts and parametric sort arguments.
HIR type checking rejects missing/free binders, sort mismatches, and cycles
without one explicit `recursive_group` label for the recursive call component.

The lowering keeps calls as function applications and emits definitions in
dependency order, so repeated call sites share one body in the SMT script.
Definitions are lowered after global declarations exist. Defined bodies that
contain `GLOBAL` constraints are currently rejected: some global rewrites can
introduce witnesses whose scope would be shared across helper calls. Target-only
helpers must be defined and set `auxiliary=true`; uninterpreted auxiliaries are
rejected because their hidden interpretation has no source-level beta
projection. Frontend-facing contracts retain helper signatures in the target
model while omitting them from source symbols and
observable beta projections. The following relational-core-to-SMT stage keeps
them in its source signature so pipeline composition remains exact.

`ParserToHir::lift(model, diagnostics, true)` retains ordinary nonrecursive
`define-fun` bodies and formal binders. The two-argument call preserves the
existing equation encoding. Unbounded SyGuS uses body retention so an ordinary
helper does not become an unnecessary universally quantified axiom. Explicit
`define-funs-rec` groups retain their group binding scope in HIR and SMT output;
standalone recursive definitions continue to use the existing axiom encoding.

Definitions introduced by a lowering pass need their own signature-extension
stage. `translate()` inserts
`typed-relational-core-defined-helper-extension-v1` between the frontend's
relational core and ordinary SMT lowering. Its source signature remains the
frontend's immutable snapshot. Only fresh, typed, acyclic auxiliary functions
with bodies may extend that signature; undeclared functions, cycles, name
collisions, and changes to existing symbol signatures are rejected.

Each new helper contributes its universal defining equation. Equation parameters
are renamed when necessary to avoid capturing a free global identifier. The
stage preserves the intermediate coordinates required by the preceding source
projection and omits the new helper interpretations. It also preserves the
decision task and objective order. The stage is visible in the translation
report, including when its source and target institutions are both the relational
core.

The mathematical reason for permitting this extension is that fresh acyclic
definitions determine unique helper interpretations for each old interpretation,
in dependency order. This does not prove the separate transformation of the
constraints that call those helpers. Those rewrites retain their own semantic
test obligations, and the contract checker does not turn structural validation
into a proof or grant a model-count guarantee.

For example, a sufficiently large unbound `cumulative` constraint shares a
single exact load-at-time function instead of constructing every task/event
pair separately. Nonnegative duration, demand and capacity conditions remain
inside the Boolean relation, including under negation. Expressions with lexical
binders keep the ordinary expansion so a helper cannot escape its binding scope.
