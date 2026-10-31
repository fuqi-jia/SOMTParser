# Source-preserving repair

Keep source, context, schema and objective specification fixed. Save each
candidate before repair; export only a selected complete snapshot.

| Failure | Repair | Do not do |
|---|---|---|
| Invalid fields | Follow live schema; omit caller-owned context | Invent APIs or change language |
| Bad source span | Recompute Unicode offsets | Change source or use byte offsets |
| Fragment absent from program | Copy a relevant emitted formula verbatim | Copy the source quotation |
| Undeclared symbol / wrong sort | Correct scope, declarations and justified coercions | Alter the mathematical domain |
| Nonempty unresolved | Examine actual competing readings against input | Clear genuine uncertainty to pass |
| Unsupported operation | Use an exact supported encoding with valid preconditions | Drop or weaken a constraint |
| Large expansion | Factor exact common terms; compact primitives | Omit rows, shrink bounds, add symmetry restrictions |
| Authentication/quota/network | Record transport failure separately | Treat it as a modeling error |

An explanation or settled ordinary reading is not an unresolved question.
Establish why source/context settles it before removing that entry. Never move
a genuine remaining ambiguity into assumptions merely to pass validation.

After any repair re-audit domains, independent clauses, every data row, optional
presence conditions, objectives and links. Return the entire replacement model,
not a patch losing earlier constraints. Respect the caller's attempt budget.

The public repair API supplies the previous candidate and located construction
diagnostics. The manual bridge supports fresh `validate` directories. Neither
may consult gold formulas, labels or semantic counterexamples during held-out
evaluation. A valid candidate stops construction repair; it is not guaranteed
semantically correct. Do not automatically repeat uncertain-billing timeouts.
