# Named integer constants (`const id = ...`, read back as `$id`) are a
# statement form outside the procedure core; refused by name rather than
# silently mis-scoped.
const two64 = 2**64;

proc main(uint64 x) =
{ true && true }
{ eqn x = x && rng true }
