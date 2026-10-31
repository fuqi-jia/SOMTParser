enum Orientation = {Upright, Clockwise, UpsideDown, Anticlockwise};
var 1..3: p;
array[Orientation] of var int: x =
    [Anticlockwise: p + 3, Clockwise: p + 1, Upright: p, UpsideDown: p + 2];
constraint x[Clockwise] = 2;
solve satisfy;
