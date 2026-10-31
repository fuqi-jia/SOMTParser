// The labels listed in a goto must all be defined in the same implementation
// body (This is Boogie 2 §9.5) -- an undefined one is a type error naming it.
procedure P() returns (r: int)
  ensures true;
{
  r := 0;
  goto Missing;
}
