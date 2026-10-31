// A fact is known after the join only when it holds on BOTH paths. The join
// is `ite(c, then, else)` per disagreeing variable (This is Boogie 2 §9.7's
// desugaring: each branch under an assume of the guard or its negation).
// r is x or -x depending on the branch; r >= 0 holds after the join because
// it holds on both.
procedure P(x: int) returns (r: int)
  ensures r >= 0;
{
  if (x >= 0) { r := x; } else { r := -x; }
}
