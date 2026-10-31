# inlinespec is semantically inline but verified through the contract
# (doc/cryptoline.pdf): assert the precondition, havock the outputs AND the
# body's assigned variables, assume the postcondition.
proc dbl(uint8 a; uint8 r) =
{ true && rng a <=u 100 }
adds c r a a;
{ true && rng r <=u 200 }

proc main(uint8 x) =
{ true && rng x <=u 50 }
inlinespec dbl(x, y);
{ true && rng y <=u 200 }
