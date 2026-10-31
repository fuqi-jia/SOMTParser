# Ghost variables are specification-only: one cannot be an instruction
# operand (typecheck/std.ml: defined_atom draws from program variables only).
proc main(uint8 x) =
{ true && true }
ghost g@uint8 : g = x && g = x;
mov y g;
{ true && rng true }
