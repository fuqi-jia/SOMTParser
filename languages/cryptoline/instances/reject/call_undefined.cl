# A call names an earlier-declared procedure; an unknown callee is a parse
# error (parsers/common.ml: parse_call_at).
proc main(uint8 x) =
{ true && true }
call nosuch(x);
{ true && rng true }
