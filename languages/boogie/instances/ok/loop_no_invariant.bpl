procedure L(n: int) returns (s: int)
  requires n >= 0;
  ensures  s >= 0;
{
  s := 0;
  while (s < n) { s := s + 1; }
}
