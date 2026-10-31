# Upstream corpus — TPTP

Unmodified `.p` files from **fitelson/ulrich-JAR** — the three TPTP inputs for
"Applying Saturation-Based Theorem Proving to Open Problems in Positive
Implicational Logic".

- Source: https://github.com/fitelson/ulrich-JAR
- Retrieved: 2026-08-17
- Licence: MIT. Unmodified.

**Three files, and the smallness is the honest part.** The TPTP Problem Library
itself is the corpus this frontend wants — thousands of problems, graded by
difficulty, in the format's own canonical form — and it is not vendorable from
here: it is distributed from tptp.org rather than a repository, and
`docs/languages-scoping.md` §1.2 and §1.7 already record its licence terms as
**not confirmed**. Vendoring files whose terms have not been read would be worse
than having three.

What these three are is real TPTP written by researchers doing the thing TPTP
exists for: refuting candidate axioms in implicational logic, in CNF, generated
for Vampire. They are not a reader's test set and not a tutorial.

## 3 of 3

All three translate. That is a weaker result than a failure would have been, and
it is worth saying why it still earns its place: this frontend's CNF and FOF
support was built against hand-written fixtures, and the standing question was
whether it had been built against a shape only its author would write. Three
files from outside say "not obviously", over a fragment — CNF with `include`-free
axioms and a conjecture — that is the fragment this frontend claims.

The claim it does **not** support is the typed dialects: `tff` and `thf` are
refused by name, `tff` being reachable and `thf` not fitting the HIR at all
(`tptp.md` §4). Nothing here exercises those, so nothing here says anything
about them.
