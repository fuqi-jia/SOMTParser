// A loop formed by goto. The reference accepts these and verifies with an
// implicit `invariant true` at the header: the back edge is cut and the
// cycle's assignments are havoc'd (RemoveBackEdges.cs). So after the loop
// nothing is known about i -- but n, which the cycle never touches, keeps
// its fact. (This is This is Boogie 2 §9.5's canonical goto-loop shape.)
procedure P(n: int) returns (r: int)
  requires n >= 0;
  ensures  n >= 0;
{
  var i: int;
  i := 0;
Head:
  if (i < n) {
    i := i + 1;
    goto Head;
  }
  r := 0;
}
