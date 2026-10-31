# ssplit demands a signed source; an unsigned one is ill-formed.
proc main(uint8 x) =
{ true && true }
ssplit h l x 4;
{ true && true }
