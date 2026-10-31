# Vector types (`uint64[4]`) and vector variables (`%v`) are an
# implementation extension (parsers/cryptolineParser.mly: vectyp, VEC_ID)
# outside the manual's grammar; the scalar core refuses them by name.
proc main(uint64[4] %v) =
{ true && true }
{ true && true }
