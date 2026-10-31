# An actual parameter used as input AND output gets its entry value captured
# by a fresh ghost variable, so the assumed postcondition can relate the
# output to the input's call-time value (parsers/common.ml: parse_call_at
# mk_ghost_instr_for_actuals). Without the ghost copy the substitution would
# read the havocked output on both sides -- `x = x`, a tautology -- and the
# caller's postcondition would have a counterexample. (A contract relating
# the output to the entry input by +1 would instead collapse to the
# inconsistent `x = x + 1` and vacuously "verify" -- the unsound direction
# this fixture's verdict pins.)
proc ident(uint8 a; uint8 r) =
{ true && rng true }
mov r a;
{ true && rng r = a }

proc main(uint8 x) =
{ true && rng x <=u 50 }
call ident(x, x);
{ true && rng x <=u 51 }
