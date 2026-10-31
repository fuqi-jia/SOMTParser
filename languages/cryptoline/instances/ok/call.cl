# A procedure call is replaced by the callee's pre-/post-conditions
# (doc/cryptoline.pdf: "The call is replaced by the pre-/post-conditions of p
# for verification"): the caller ASSERTS the precondition (an obligation at
# the call site), havocs the outputs, and ASSUMES the postcondition.
proc dbl(uint8 a; uint8 r) =
{ true && rng a <=u 100 }
adds c r a a;
{ true && rng r <=u 200 }

proc main(uint8 x) =
{ true && rng x <=u 50 }
call dbl(x, y);
{ true && rng y <=u 200 }
