# inline splices the callee BODY at the call site with the actuals
# substituted for the formals (doc/cryptoline.pdf) -- so the body's
# instruction safety is checked at the call site, which the contract-only
# `call` does not do.
proc dbl(uint8 a; uint8 r) =
{ true && rng a <=u 100 }
adds c r a a;
{ true && rng r <=u 200 }

proc main(uint8 x) =
{ true && rng x <=u 50 }
inline dbl(x, y);
{ true && rng y <=u 200 }
