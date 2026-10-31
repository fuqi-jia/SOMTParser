# Upstream corpus — WCNF (weighted MaxSAT)

Unmodified files from `jjasferreira/maxsat-core-bench`, the 25 smallest `.wcnf`
instances (all at most 300 KB; the repository's largest is 15 MB and is not
vendored). They come from its `tests/mse12/` and `tests/mse24/` directories.

- Source: https://github.com/jjasferreira/maxsat-core-bench
- Retrieved: 2026-09-21
- Licence: **MIT**, stated in the repository's `LICENSE` (Copyright (c) 2026
  José João Ferreira).

## A caveat on provenance, recorded rather than glossed

The repository states MIT for itself, and that is an established licence
statement, which is what D29 asks for. But the *instances* are named for the
MaxSAT Evaluations of 2012 and 2024 (`tests/mse12/`, `tests/mse24/`), and the
repository does not say where it obtained them or under what terms the
evaluation distributed them. So the MIT covers the repository; it does not by
itself settle the instances' own origin.

This is recorded because the difference matters if these files are ever
redistributed further or used in a published table. It is not treated as a
blocker for use inside this tree, where the repository's own stated licence is
the best evidence available.

## Audit on 2026-09-21 — and the defect this corpus found

**25 of 25 translate.** Fifteen did on the first attempt; the other ten were
refused with `E_PARSE`, and the refusal was the reader's fault rather than the
files'.

A DIMACS-family comment is a line whose **first character** is `c`. The space
after it is conventional, not required, and the MaxSAT Evaluation's own
standardised instances open with

    c Standarized MaxSat Instance
    c{
    c "sha1sum": "7541f4ae…",
    c "nvars": 91,

-- a JSON metadata block written one line at a time, with no separator after
the `c` on the brace lines. The reader split each line on whitespace and
compared the first *token* to `"c"`, so `c{` matched nothing and was read as a
malformed clause. A well-formed file was reported as malformed input, which is
the wrong bucket as well as the wrong answer.

`languages/dimacs` had the same defect, reached by the same shape, and was
fixed with it. Neither was reachable from any hand-written fixture in the tree:
finding it is what vendoring a real corpus is for.
