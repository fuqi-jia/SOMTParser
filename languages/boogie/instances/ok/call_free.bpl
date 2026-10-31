// Free contract clauses (This is Boogie 2 §8.2): a free requires is assumed
// by the implementation and IGNORED at call sites (not asserted); a free
// ensures is assumed at call sites and not asserted at the body. Treating a
// free clause as checked is wrong in the direction that reports sat on a
// program that verifies.
//
// Id's free requires x >= 0 lets P call it on an unconstrained a. If the
// clause were asserted at the call site, this program would NOT verify.

procedure Id(x: int) returns (y: int);
  free requires x >= 0;
  ensures  y == x;

procedure Q(x: int) returns (y: int)
  free ensures y == 12345;
{
  y := 0;
}

procedure P(a: int) returns (b: int)
  ensures b <= 0;
{
  call b := Id(a);
  assume b <= 0;
}
