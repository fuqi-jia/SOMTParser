% Every connective the format has, over one signature.
fof(a, axiom, p & q).
fof(b, axiom, p | r).
fof(c, axiom, p => q).
fof(d, axiom, q <= p).
fof(e, axiom, p <=> q).
fof(f, axiom, r <~> s).
fof(g, axiom, ~ (r ~& s)).
fof(h, axiom, ~ (r ~| s)).
fof(i, axiom, ? [X] : (f(X) = g(X) & f(X) != a)).
