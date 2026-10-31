string: block = concat(["#" | i in 1..3]);
constraint block = "###";
solve satisfy;
