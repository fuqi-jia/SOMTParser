# Upstream corpus — MoXI

Unmodified `.moxi` files from **moxi-mc-flow**, `test/moxi/` — 30 of the 55
there, excluding `test/moxi/Bad/`, which holds deliberately malformed input.

- Source: https://github.com/ModelChecker/moxi-mc-flow/tree/main/test/moxi
- Retrieved: 2026-08-17
- Licence: **GPL-3.0**. Noted prominently because it is the only corpus here
  under a copyleft licence: redistribution is permitted and carries the GPL's
  obligations, which matters if this subsystem is ever published. The files are
  unmodified and are inputs rather than linked code.

## Where it stands: 17 of 30, and no engine message reaches the reader

The count is 17 translated, 13 refused (2026-09-19). Subsystem flattening,
enums, rigid `declare-const`/`define-fun`, and parametric
`declare-datatype`/`declare-datatypes` all landed. Every remaining refusal is a
named `E_UNSUPPORTED_CONSTRUCT` with its reason. Earlier history: **the four
files that leaked a raw engine message now translate**, and they leaked because
of three misreadings of `check-system` rather than three missing features.
`docs/open-questions-2026-08-13.md` D33 has the detail; in short:

- **A condition carries a NAME.** `:reachable (rch (= o #b00001010))` was
  asserted whole, so `rch` became a function applied to an equality and the
  engine said `Unknown or unexpected symbol "rch"` — about a generated script,
  for a file whose own text is fine.
- **A `check-system` restates the interface under its own names.**
  `:input ((i ...))` against the system's `:input ((in ...))` *identifies* `i`
  with `in` positionally. One variable, not two joined by an equation — the trap
  `moxi.md` §4.2 records for a subsystem's argument list, one level up. `i` was
  the other leak.
- **A condition the query does not name is not checked.** §2.4 says so and the
  frontend translated everything it found. No corpus could have shown this: a
  file asking about all its conditions and a file whose extras were translated
  anyway produce the same output. Found by reading this project's document
  against its code.

A fourth defect was in the engine's shared machinery rather than in MoXI, and
`QF_ABV_ConstArray.moxi` is the file that found it: renaming a formula to a step
rebuilt every operator through `mkOp`, which **cannot carry an operator's
indices**, and for `((as const (Array T U)) v)` — whose sort is not derivable
from its argument — aborted outright. Three frontends had written that
substitution separately and all three had the same two bugs; there is now one
`Hir::substituteIdents`. D34.

## What still blocks the other thirteen (2026-09-19)

All thirteen are named refusals, none a frontend gap:

- **7 files define systems and never `check-system` them** (`QF_LIA_*`,
  `QF_LRA_*`, `QF_NIA_Silly`, `QF_NRA_Silly1/2`): library files; asking
  nothing is legitimate and there is nothing to translate.
- **4 files need an explicit selector**: `QF_BV_DoubleDelayTwoCheck` (two
  `check-system` commands; pass `check_index=<n>`) and
  `QF_BV_DoubleDelayTwoQuery`, `QF_LIA_DoubleDelay1`, `QF_LRA_DoubleDelay1`
  (two queries each; pass `query=<name>`). Translating them together would
  answer a question the file did not ask, so the refusal is the default, not
  the only option.
- **1 file selects `:fairness`** (`QF_BV_ModCounterFair`): a liveness
  assumption a bounded unrolling cannot express; permanent.
- **1 file carries upstream's own NOT-SUPPORTED header**
  (`QF_LRA_LossyIntChannelX`): it also defines `LossyRealChannel` twice, asks
  nothing, and writes the datatype's constructor list without the parens the
  SMT-LIB grammar requires (z3 rejects that spelling too). The
  `declare-datatype` command itself is read since 2026-09-19 — the file fails
  for its own reasons, and `instances/ok/datatype_channel.moxi` is its
  spec-well-formed shape as a working example.

Earlier clusters, now closed: the twelve multi-`define-system` files flattened
via §4.2 instantiation; the five `declare-enum-sort` files rewrite to SMT-LIB
`declare-datatypes`; the three `declare-const` and three `define-fun` files are
rigid environment declarations.

## What the corpus found, in order


**A raw engine message reaching the user as the first diagnostic**, with no
`ErrorCode` attached.

A MoXI file's formulas are handed to the engine's SMT-LIB parser as a generated
script. Anything this frontend did not declare into that script therefore
surfaces as the *engine's* complaint — `Unknown or unexpected symbol "State" in
line 1` — naming a symbol that is perfectly well declared one line earlier in
the file the reader is looking at, and pointing at a line number in a script the
reader has never seen.

Twelve files hit it via `(declare-enum-sort State (Start Active Done))`. That
command is now refused where it is met and by its own name, along with
`declare-const`, `define-fun` and `declare-datatypes`. An enumeration *is*
reachable in principle — the engine has algebraic datatypes and an enumeration
is a datatype whose constructors are all nullary — but the mapping has to reach
the system's declarations, the primed copies and the `check-system`'s own
declaration list, which is the frontend's sort table rather than one line.

Four files went on leaking an engine message after that, on
`:reachable (rch ...)` and on a `check-system`'s `:input` names. Naming it as a
class rather than as four files is what made it findable: the property test in
`test_upstream_corpus.cpp` grades the first ERROR for `E_INTERNAL` and for being
longer than twenty characters, and **a raw engine message passes both** while
telling the reader about a script that does not exist on disk. So the grader
could not see the thing the corpus was showing.

All four now translate, and the cause was not four missing features but three
misreadings of `check-system` plus one defect in the engine's shared
substitution — the summary at the top of this file, and D33/D34 for why each was
invisible to the instrument that should have caught it.
