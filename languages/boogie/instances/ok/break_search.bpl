// `break` is a forward exit: This is Boogie 2 §9.5 desugars it to a goto to
// the loop's Done. The continuation joins the exit edge (guard false, i is n)
// with the break edge (i arbitrary-but-invariant-satisfying), so i <= n holds
// after the loop on every path.
procedure P(n: int) returns (i: int)
  requires n >= 0;
  ensures  i <= n;
{
  i := 0;
  while (i < n)
    invariant i <= n;
  {
    if (*) { break; }
    i := i + 1;
  }
}
