// A goto with several targets chooses BLINDLY between them (This is Boogie 2
// §9.5), so the join at Done has two edges whose guards are not exclusive --
// the encoding gives each edge a fresh gate boolean (the passified-CFG
// discipline), and r after the join is 1 or 2.
procedure P() returns (r: int)
  ensures r == 1 || r == 2;
{
  goto A, B;
A:
  r := 1;
  goto Done;
B:
  r := 2;
Done:
}
