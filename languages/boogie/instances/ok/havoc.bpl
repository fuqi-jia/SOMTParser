// havoc is the language's non-determinism primitive: after it, nothing is
// known about x. Translating it as a no-op leaves the old value in place and
// the postcondition below would then "verify".
procedure H(a: int) returns (y: int)
  requires a == 3;
  ensures  y >= 0;
{
  var x: int;
  x := a;
  havoc x;
  assume x >= 0;
  y := x;
}
