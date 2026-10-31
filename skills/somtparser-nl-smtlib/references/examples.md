# Executable three-route example

`examples/scheduling/` contains the same Chinese three-task scheduling problem
and three complete candidates. All start times are integers in 0..6, durations
are 2/3/1, endpoint contact is allowed, and the last completion time is minimized.

```sh
python scripts/ir2smt.py examples/scheduling/hir.json --source examples/scheduling/problem.txt --route hir --mode code
python scripts/ir2smt.py examples/scheduling/smtlib2.json --source examples/scheduling/problem.txt --route smtlib2 --mode code
python scripts/ir2smt.py examples/scheduling/hybrid.json --source examples/scheduling/problem.txt --route hybrid --mode code
```

The HIR candidate uses native `no_overlap` plus the exact `makespan` macro. The
direct candidate declares and encodes the whole model in SMT. The hybrid keeps
no-overlap/domains/objective in HIR and uses one SMT equality to define its
HIR-declared makespan variable. Thus its SMT extension contributes real semantics,
not a decorative duplicate. No route executes a solver during translation.

For scripts emitting the final response and model providers emitting input
candidates, the interfaces differ. See [provider-candidates.md](provider-candidates.md)
for minimal native HIR/direct candidate syntax; [output-contract.md](output-contract.md)
for the generator's machine-readable response. References are development examples,
not reported benchmark cases or a guarantee of future LLM accuracy.
