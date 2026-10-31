// A `goto` into a structured statement's body is refused by name: the
// encoding joins control flow at construct boundaries, and jumping into the
// middle of a branch has no join to arrive through.
procedure P() returns (r: int)
  ensures r >= 0;
{
  goto L;
  if (true) {
L:
    r := 1;
  }
}
