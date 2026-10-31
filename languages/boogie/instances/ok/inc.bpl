// The running example of docs/languages/boogie.md §2.3.
procedure Inc(x: int) returns (y: int)
  requires x >= 0;
  ensures  y == x + 1;
{
  y := x + 1;
}
