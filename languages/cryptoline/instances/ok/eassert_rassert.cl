# eassert/rassert assert one side of the predicate only (parsers: EASSERT,
# RASSERT); each becomes an obligation of its own side's fragment.
proc main(uint8 x, sint8 y) =
{ true && true }
eassert x + 0 = x;
rassert x = x;
{ eqn x = x && rng x = x }
