// `if (*)` is the demonic choice: either alternative may run, so a fact holds
// after it only if it holds on every alternative. The condition is a fresh,
// unconstrained boolean, and the join's ite is exact because the branch
// guards are that boolean and its negation.
procedure P() returns (r: int)
  ensures r == 0 || r == 1;
{
  if (*) { r := 0; } else { r := 1; }
}
