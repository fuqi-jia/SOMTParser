(* The document's own example, at 8 bits so the model stays small.
   `mull` produces a double-width product as two registers and `adds`
   produces a carry -- both are data the postcondition reads. *)
proc mul_add (uint8 a, uint8 b, uint8 c) =
{ true && true }
mull carry prod a b;
adds overflow sum prod c;
{ eqn sum + overflow * 2**8 = 0 && rng true }
