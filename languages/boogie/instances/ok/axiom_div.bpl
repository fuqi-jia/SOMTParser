// Boogie's div and mod are SMT-LIB's, which is Euclidean -- §4.5, and this is
// the one frontend in the batch that names EUCLID rather than TRUNC.
const g: int;
axiom g > 0;
procedure D(n: int) returns (q: int)
  requires n >= 0;
  ensures  q >= 0;
{
  q := n div 2;
}
