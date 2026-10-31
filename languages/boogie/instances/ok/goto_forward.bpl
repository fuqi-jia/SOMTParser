// A forward `goto` is the canonical early exit (This is Boogie 2 §9.5's
// desugaring of `break`). The two paths join at Done, and a fact survives
// only when true on both.
procedure P(x: int) returns (r: int)
  ensures r >= 0;
{
  var t: int;
  t := x;
  if (t < 0) { goto Neg; }
  r := t;
  goto Done;
Neg:
  r := -t;
Done:
  assert r >= 0;
}
