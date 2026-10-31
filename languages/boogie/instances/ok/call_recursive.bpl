// A recursive call is just a contract instantiation: the registry sees the
// procedure's signature before its body is read, so the recursive call
// asserts the same requires and assumes the same ensures it is itself
// verified against. Boogie does not check termination; the contract reading
// is sound without it (This is Boogie 2 §9.9).

procedure Wrap(n: int) returns (r: int)
  requires n >= 0;
  ensures  r >= 0;
{
  call r := Wrap(n);
}
