# Upstream corpus — DIMACS CNF

Unmodified files from **CaDiCaL**, `test/cnf/`.

- Source: https://github.com/arminbiere/cadical/tree/master/test/cnf
- Licence: MIT (Armin Biere)

Selected smallest-first and capped by size; the point is coverage of the
constructs the format's own users write, not scale.

These are exercised by `test/languages/test_upstream_corpus.cpp` as a property
rather than as cases: every file must translate, or refuse with a reason that
names the construct, and what it emits must re-parse.
