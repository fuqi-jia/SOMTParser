(* An assume is a hypothesis the proof may use; an assert is an obligation.
   Swapping them makes the verification vacuous. *)
proc hyp (uint8 x) =
{ true && true }
assume { rng x <= 4 }
mov y x;
assert { rng y <= 4 }
{ rng y <= 4 }
