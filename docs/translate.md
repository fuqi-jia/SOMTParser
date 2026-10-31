# Translation API

`somtparser.translate` is the single file/source translation entry point. It
returns `Translation`, combining completed output with the checked model and
its structured report. Python calls the C++ implementation directly. No
translation executable or console script is built or installed.

```python
import somtparser as sp

m = sp.translate("partial.mzn", language="minizinc", profile="default",
                 dialect="z3", report="report.json")
assert m.exit_code == 0, m.diagnostics
p = sp.parse(m.smt2)
p.dump_smt2("partial.oms.smt2", sp.OmtDialect.OptiMathSAT)
```

## Parameters

```python
translate(path="", *, source="", language="", profile=None, dialect=None,
          data=(), options=None, strict=False, module=False, report="",
          stdin=None, output=None, diagnostics=None, details=True) -> Translation
```

| Parameter | Meaning |
| --- | --- |
| `path`, `source` | Main input file or inline text; nonempty `source` takes precedence |
| `language` | Registered ID; empty detects from the file |
| `profile` | Encoding profile; `None` selects `default` |
| `dialect` | `gomt` (alias `smtlib-omt-2025`), `z3`, `optimathsat`, `none`, or `OmtDialect`; `None` selects GOMT |
| `data` | Companion file paths, in order |
| `options` | Frontend option names mapped to string values |
| `strict` | Raise `TranslationError` on a nonzero status; otherwise return a result |
| `module` | Export a query-free library/open model; leave profile/dialect unset |
| `report` | JSON destination path; empty disables writing; module mode writes its interface |
| `stdin` | Text input stream for `path="-"`; defaults to `sys.stdin` and requires `language` |
| `output`, `diagnostics` | Caller-owned text streams; `None` captures the respective result channel |
| `details` | Build and retain optional inspection/audit information; defaults to `True` |

Paths accept strings or `os.PathLike`. Streams are flushed, never closed.
Captured output is silent. A streamed channel has an empty corresponding result
string, avoiding a second copy of a large output. For byte-stable file output,
open with `encoding="utf-8", newline=""`.

## Result and inspection

Every call returns the same `Translation` type, including failures and calls
with `details=False`. The completed channels are `smt2: str`,
`diagnostics: str` and `exit_code: int`. Diagnostic formatting, source locations,
severity/error-code names, final newlines, and output/report serialization
retain the former file-conversion contract. `diagnostic_items` exposes the
structured diagnostic objects; code previously inspecting the diagnostic list
should use that property.

| Status | Meaning |
| --- | --- |
| `0` | Translation and requested output/report writing succeeded |
| `1` | Translation/export failure, including input-file I/O diagnostics |
| `2` | Invalid settings, such as unknown IDs or incompatible module settings |
| `3` | Input-stream, output-stream or report-destination I/O failure |

`ok` records whether the checked translation pipeline succeeded; `exit_code`
also accounts for subsequent report/output faults. With `details=True`,
`report` is a `TranslationReport`, `parser` exposes the materialized SMT DAG,
and `to_smt2(dialect=...)` / `write_smt2(path, dialect=...)` retain their export
interfaces. Packed translations and query-free modules do not expose a full
Parser and raise a clear error on access. Module exports preserve their native
query-free output and do not support dialect changes.

## Lightweight results

```python
m = sp.translate("model.mzn", dialect="z3", details=False)
assert m.report is None
smt2 = m.smt2
```

Turning off details does not change SMT bytes, diagnostic bytes or the status
code. Type checking, semantic contracts, fidelity gates and objective/export
validation still run. Optional encoding-choice audit records, semantic-stage
presentation strings, feature-count maps, provenance hashes and the report-only
DAG counting traversal are omitted. Once output is complete, inspection DAGs,
HIR, lowering indexes and semantic/audit structures are released. This saves
retained memory and report/statistics work; required translation/validation
structures still exist temporarily. No fixed speedup or memory reduction is
promised across all languages.

An explicit `report` path requests JSON construction/writing even with
`details=False`, so it reduces those savings. The returned `report` still stays
`None`. Report timing measurements naturally vary between executions.

Accessing `parser` or native inspection with details disabled raises an error
instructing the caller to translate with `details=True`. A retained `smt2` can
be re-read for the selected dialect; another dialect requires `details=True`.
If output was streamed, it is not retained for later export in lightweight
mode, and attempting that export also raises a clear error.

```python
with open("model.smt2", "w", encoding="utf-8", newline="") as output:
    m = sp.translate("model.btor2", profile="bmc", dialect="z3",
                     options={"bmc_depth": "10"}, output=output, details=False)
assert m.exit_code == 0, m.diagnostics
```

`HirBuilder.translate(profile="default", dialect=None, details=True)` returns
the same `Translation`. Its existing default dialect remains Z3. This choice
also applies to direct native HIR model translation.

## Experiment and C++ integration

Replace a subprocess's returncode/stdout/stderr with
`m.exit_code`, `m.smt2`, `m.diagnostics`. Keep hard timeouts, per-instance memory
limits and process isolation in the experiment worker. The JSON format is
unchanged; measured timing fields vary naturally between runs.

```cpp
#include <somtparser/translation/translate.h>
#include <somtparser/languages/register_all.h>

SOMTParser::Lang::registerAllLanguages(SOMTParser::Lang::LanguageRegistry::instance());
SOMTParser::Lang::SourceUnit source;
source.main_path = "model.mzn";
SOMTParser::TranslateOptions options;
options.language_id = "minizinc";
options.omt_dialect = SOMTParser::Lower::OmtDialect::Z3;
options.details = false;
auto m = SOMTParser::translate(source, options);
// m.exitCode(), m.smt2(), m.diagnosticText(), m.ok(), m.hasDetails()
```

Link `SOMTParser::languages` for textual frontends; the core `translate` also
accepts a typed HIR model. For caller-owned streams use
`translate(source, options, &input, &output, &diagnostics)`; omitted stream
pointers capture output or select `std::cin`. Report paths use
`options.report_path`. With details disabled, `report()` and `parser()` throw
clear inspection errors; `hasDetails()` reports availability.
