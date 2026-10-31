# Upstream corpus — CryptoLine

Unmodified files from **CryptoLine**, `examples/tests/` — all 17 of them.

- Source: https://github.com/fmlab-iis/cryptoline/tree/master/examples/tests
- Retrieved: 2026-08-17
- Licence: MIT (Formal Methods Laboratory, Academia Sinica). The files are
  unmodified.

`examples/tests/` deliberately, not `examples/` at large. The wider tree holds
real verification inputs — FourQ, SIDH P503/P751, blst — which are hundreds of
lines of machine-generated straight-line code and stop on the same one or two
constructs the small ones do, only later. The unit tests are the format's
authors exercising one instruction each, which is what a corpus is for at this
stage.

## Where it stands: 17 of 17

All files translate as of 2026-08-25. This moved only after the frontend was
checked against CryptoLine's own `doc/cryptoline.pdf`, `qfbv/common.ml`,
`verify/smt.ml`, and `typecheck/std.ml`; the rules were not inferred from
instruction names.

The corpus exposed semantic, not merely syntactic, omissions:

- annotated `name@type` declarations and typed hexadecimal/binary constants;
- carry versus borrow (`subc`/`subs` versus `subb`) and carry-in arithmetic;
- the different result widths of `split` and `spl`;
- output and combined shifts, rotations, `join`, `mulj`, `seteq`, and `setne`;
- instruction safety obligations, which are independent of assignment graphs;
- range shifts, extensions, modular equalities, and `w+1`-bit
  `equmod`/`eqsmod`/`eqsrem` semantics;
- `vpc` as cast plus value-preservation safety, and instruction-level
  `assert/assume` predicates with operational `prove with` hints.

This result is a regression floor for the 17 compact reference examples, not a
claim of full-language support. `cut`/`ecut`/`rcut`, procedures and inlining,
ghost/vector syntax, explicit `u*`/`s*` variants, and the remaining expression
catalogue are still rejected or absent as documented in
`docs/languages/cryptoline.md`.
