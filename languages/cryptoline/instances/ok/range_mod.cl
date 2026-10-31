proc main(uint8 x) =
{ true && true }
assert true && and [equmod x 0@8 3@8,
                    eqsmod x 0@8 3@8,
                    eqsrem x 0@8 3@8]
  prove with [qfbv solver boolector];
{ true && true }
