(* `x` is assigned twice. The second assignment defines a new value, and the
   postcondition means the second -- a translation reusing one variable makes
   the two assignments contradictory and the whole query trivially unsat. *)
proc ssa (uint8 a, uint8 b) =
{ true && true }
mov x a;
mov x b;
{ eqn x = 0 && rng true }
