# Translation output

`Translation.to_smt2()` returns a complete SMT/OMT script as a Python string.
For large scripts, `Translation.write_smt2(path, dialect=...)` writes the
script directly to a file and reports destination-open or write failures as
exceptions. A failed `Translation` or unsupported objective dialect is rejected
before an existing destination is opened or truncated.

Both APIs use the same emitter. Declarations, recursive functions, datatypes,
named assertions, soft assertions, and objectives retain their normal ordering;
objective commands are written before the dialect's query. The string-returning API
still necessarily allocates its result string. The streaming path also applies
to `Parser.dump_smt2(path)`. Individual parser assertion terms and the
objective-command block are still rendered as strings by their existing
term/objective emitters.

## Three optimization dialects

The same native parser state or HIR translation can be exported as
`OmtDialect.Z3`, `OmtDialect.OptiMathSAT`, or `OmtDialect.Gomt`.
`SmtLib2025` remains a compatibility alias for `Gomt`.

```python
import somtparser as sp

parser = sp.parse("(declare-const x Int)(assert (>= x 2))"
                  "(minimize x)(check-sat)(get-objectives)")
for dialect, path in [(sp.OmtDialect.Z3, "z3.smt2"),
                      (sp.OmtDialect.OptiMathSAT, "optimathsat.smt2"),
                      (sp.OmtDialect.Gomt, "gomt.smt2")]:
    parser.dump_smt2(path, dialect=dialect)
```

`somtparser.translate(path, dialect="z3")` selects the same dialects for
language translation; see [the conversion API](translate.md).
`Parser.dump_smt2()` defaults to Z3;
`Translation.to_smt2()` retains the dialect selected at translation time.

Z3 uses `minimize`, `maximize`, `assert-soft`, and `check-sat`. OptiMathSAT
also explicitly activates soft groups with `minimize`; invoke its executable
with `-optimization=true`. GOMT uses named `define-objective` and
`define-maxsmt-objective` definitions, a `define-multi-objective` when needed,
and one `optimize-sat` query. A terminal `get-objectives` is mapped to
`get-value` on the GOMT leaf objective names. Objective directions, ordering,
soft weights and group membership are part of the export contract.

GOMT here follows the authors' [SMT 2025 proposal](https://ceur-ws.org/Vol-4008/SMT_paper25.pdf),
not an adopted SMT-LIB standard. Native readback supports Int/Real, bit-vector and floating-point objectives
with their default orders, MaxSMT leaves, and flat compound objectives. Nested compounds, custom order
encodings and objective declarations inside pushed scopes are rejected.
Vendor dialects reject combinations they cannot represent.

The native dump is a snapshot of the current assertions and objectives with
the terminal response requests. It does not replay earlier checks and scope
changes; use the ordered command API for that history. `None` is an explicitly
weakened feasibility mode on Translation, not a fourth optimization dialect;
native lossless dumps refuse it when optimization goals are present.

The ordered `Command` payload retains its own `assumptions` for
`check-sat-assuming`, even after subsequent `pop` or `reset`. Its
`push_pop_level` preserves the parsed numeral (including zero); `index` is
monotonic across input chunks and scope API calls. Python also exposes
`original` for the source text of a parsed command. A snapshot uses the last
query's own assumptions, not a mutable current-context assumption list. If
those assumptions or response terms refer to declarations removed by a later
scope change, lossless snapshot export reports an error; issue a new query for
the current state or use the ordered history instead.

Allocation failure during SMT-LIB parsing propagates as `std::bad_alloc`
(`MemoryError` through Python's native bindings); the language translation
boundary reports `E_RESOURCE`. Such a failure does not establish malformed
input. Experiment drivers must likewise distinguish explicit allocation errors
from syntax rejection, and retain the original resource budget with the result.
