# Upstream BTOR2 examples

Copied verbatim from the BTOR2 reference tools, which are the format's own
implementation:

    https://github.com/Boolector/btor2tools  ->  examples/btorsim/

They are here because a hand-written fixture can only contain a construct
somebody thought to write down, and these were written by the people who
defined the format. Two coverage gaps surfaced the first time they were run —
`implies`, and the indexed `slice` — neither of which any fixture in `ok/`
exercised.

btor2tools is MIT-licensed.
