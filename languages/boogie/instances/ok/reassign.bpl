// x is assigned twice. Without SSA versioning the two equations contradict,
// the query is unsatisfiable for a reason unrelated to the property, and the
// procedure reports "verified".
procedure R(a: int) returns (y: int)
  requires a > 0;
  ensures  y > 2;
{
  var x: int;
  x := a + 1;
  x := x + 1;
  y := x;
}
