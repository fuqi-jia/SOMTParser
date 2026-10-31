include "arg_max.mzn";enum E={A,B,C};array[E] of var -9..9:a;constraint a[A]=4 /\ a[B]=9 /\ a[C]=9 /\ arg_max(a)=B; solve satisfy;
