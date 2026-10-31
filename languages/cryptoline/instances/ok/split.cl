(* split hi lo x 4 says x = hi * 2**4 + lo, and that identity has to be
   asserted -- declaring hi and lo and moving on proves nothing about x. *)
proc sp (uint8 x) =
{ true && true }
split hi lo x 4;
{ eqn hi * 2**4 + lo = 0 && rng true }
