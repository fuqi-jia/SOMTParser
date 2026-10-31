// A call is the two-sided contract at the call site (boogie.md §2.3/§4.2;
// This is Boogie 2 §8.2/§9.9), not an inlining. This fixture used to pin the
// refusal in reject/; the encoding landed on 2026-09-19.
//
// Callee is BODILESS: the contract is all a caller ever sees. The caller
// establishes the precondition (a >= 0, from its own requires), and learns
// b == a from the assumed postcondition, so b >= 0 verifies.
procedure Callee(x: int) returns (y: int);
  requires x >= 0;
  ensures  y == x;

procedure Caller(a: int) returns (b: int)
  requires a >= 0;
  ensures  b >= 0;
{
  call b := Callee(a);
}
