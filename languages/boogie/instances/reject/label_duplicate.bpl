// Labels used within the same implementation body must be distinct (This is
// Boogie 2 §9.5) -- a duplicate is a type error naming it, not a re-join.
procedure P() returns (r: int)
  ensures true;
{
  r := 0;
L:
  r := 1;
  if (*) { r := 2; }
L:
  r := 3;
}
