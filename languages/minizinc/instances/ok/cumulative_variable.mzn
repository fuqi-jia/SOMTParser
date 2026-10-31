array[-1..0] of var -10..10: start;
array[-1..0] of var 0..3: duration;
array[-1..0] of var 0..2: demand;
var 0..4: capacity;
constraint cumulative(start, duration, demand, capacity);
solve satisfy;
