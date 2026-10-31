# Datatypes in the direct HIR JSON API

A candidate may include an optional `datatypes` list. Each record has a unique
`name`, optional unique `params`, a nonempty `constructors` list, and an
optional `coinductive` Boolean. Each constructor has a unique `name` and a
`fields` list; each field has a unique `name` (the SMT-LIB selector) and a
`sort`.

Sorts use `{"Datatype":"Tree"}` for an arity-zero type,
`{"Datatype":{"name":"List","args":["Int"]}}` for a parametric
instance, and `{"Parameter":"T"}` only inside a declaration that binds `T`.
The declaration builder registers all names and arities before validating
fields, permitting forward and mutual references without inferring a scheme.
Parameter substitution is simultaneous: an inserted argument is not re-read
under another datatype's parameter names. A user `Uninterpreted` sort may not
reuse a parameter name in that declaration, since native HIR represents both
with nominal sort names.

Terms use explicit result sorts so nullary parametric constructors are not
ambiguous: `{"dt_constructor":"nil","sort":{"Datatype":{"name":"List","args":["Int"]}},"args":[]}`.
Selectors carry the declared result sort, which native HIR type checking
verifies after substituting the datatype instance's type parameters. A tester
uses `{"dt_tester":"cons","value": ...}` and has Bool sort.

Inductive recursive batches are checked by searching instantiated
constructor alternatives for a finite ground value, tracking exact instantiated datatype sorts. Structurally smaller instances such as `Box[Box[Int]]` to `Box[Int]` remain distinct; expanding parameter recursion is refused explicitly rather than searched without bound. Datatype recursion beyond 128 active instances is refused. This is constructor-aware:
`D = wrap(Box[D])` is accepted when `Box[T]` has a nullary `empty` alternative,
even if another `Box` constructor contains `T`. Unsupported array/expanding
recursion in one constructor alternative does not hide a separate productive
alternative; if no alternative proves inhabitation, the unsupported case is
reported. Sets are inhabited by
`set.empty`, tuples require every field sort to be inhabited, and arrays require
an inhabited element sort whenever the index sort is inhabited. A recursive
datatype reference beneath an array sort is refused with an explicit
unsupported-case diagnostic; it is not mislabeled as an ill-founded type.
A batch validation failure leaves the builder's declarations and name tables
unchanged. The native checker remains authoritative for field types, constructor
arity, duplicate symbols, sort closure, and mutual-recursion rules. A nested recursive parametric occurrence such as `D` containing `Box[D]`
can be productive by the constructor analysis above, but current solver
backends may still reject its SMT datatype encoding as not well-founded. In
particular, cvc5 rejects this shape both when `Box` and `D` are emitted
separately and in one declaration group. The productivity check establishes
the Python-side constructor inhabitance result, not solver acceptance for
nested-recursive encodings.

Direct declarations, constructors, selectors, testers, rollback, parameter
substitution, and deterministic NL proposal/compilation checks pass in
R37c. Those API checks are not an LLM
generation-accuracy measurement.
