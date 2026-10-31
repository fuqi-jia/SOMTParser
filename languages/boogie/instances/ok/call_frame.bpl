// The caller frame and old() at a call site.
//
// Bump's modifies clause lists g and only g, so the call havoc's g and
// leaves h ALONE: omitting the frame (havoc'ing h too, or nothing at all)
// is the §4.2 failure mode this fixture exists to catch. And `old(g)` in
// Bump's ensures is g's value at CALL entry, so after the call g == g_before + 1
// where g_before is the version the caller had in hand.
var g: int;
var h: int;

procedure Bump();
  modifies g;
  ensures g == old(g) + 1;

procedure P() returns (r: int)
  requires g >= 0 && h == 41;
  modifies g;
  ensures  r >= 1 && h == 41;
{
  call Bump();
  r := g;
}
