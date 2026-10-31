(* The two variables hold the same bits and differ only in declared
   signedness, so the algebraic half lifts them through different
   conversions. Reading both as unsigned shifts the signed one by 2**8. *)
proc sgn (uint8 u, sint8 s) =
{ true && true }
mov v u;
mov t s;
{ eqn v = t && rng true }
