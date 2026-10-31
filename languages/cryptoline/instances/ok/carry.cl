(* The carry is data: the postcondition is about it, so dropping it would
   leave a variable nothing defines. *)
proc addc (uint8 x, uint8 y) =
{ true && true }
adds c s x y;
{ eqn s + c * 2**8 = 0 && rng true }
