# The entry point of a multi-procedure program is the main procedure
# (doc/cryptoline.pdf); a program without one is malformed
# (parsers/common.ml: parse_spec raises "A main function is required.").
# A single-procedure file verifies that procedure, whatever its name.
proc helper(uint8 x) =
{ true && true }
mov y x;
{ true && rng true };

proc other(uint8 x) =
{ true && true }
mov z x;
{ true && rng true }
