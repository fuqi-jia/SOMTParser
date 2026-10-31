// A MULTI-index map. The one-index form is an SMT-LIB array and translates;
// this one is not, and the two ways to make it one -- curry it, or index by a
// tuple -- say different things about what the map is. The frontend refuses
// rather than choosing.
var heap: [int, int]int;

procedure M(i: int, j: int) returns (v: int)
  ensures v == v;
{
  v := heap[i, j];
}
