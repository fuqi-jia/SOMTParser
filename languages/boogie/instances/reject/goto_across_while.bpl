// A goto loop that crosses a `while` boundary is refused by name: the
// `while`'s checked-invariant encoding and a goto loop's implicit-true
// cut (RemoveBackEdges.cs) do not compose. Write the loop as one construct.
procedure P() returns (r: int)
  ensures true;
{
  r := 0;
Top:
  r := r + 1;
  while (r < 100) {
    goto Top;
  }
}
