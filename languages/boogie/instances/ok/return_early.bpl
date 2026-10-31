// `return` is an exit point: the checked ensures are obligations there, under
// the path that reaches it -- exactly as they are at the body's final
// fall-through. Here both exit points establish r >= 1: the early return with
// 1, the fall-through with x + 1 where the branch guard gives x >= 1.
procedure P(x: int) returns (r: int)
  ensures r >= 1;
{
  if (x <= 0) {
    r := 1;
    return;
  }
  r := x + 1;
}
