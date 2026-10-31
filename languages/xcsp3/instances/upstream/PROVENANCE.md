# Upstream corpus — XCSP3

Unmodified files from the **XCSP3 C++ parser**, `instances/`.

- Source: https://github.com/xcsp3team/XCSP3-CPP-Parser/tree/master/instances
- Licence: MIT (XCSP3 team)

`example.xml` found `<var id="yy" as="zz"/>` -- domain aliasing -- which this
frontend reported as "a variable has an empty domain": true of the element and
the wrong thing to tell the author. Scalar and array aliases now resolve to the
same domains/shape and declare distinct observable variables. The `as` attribute
copies domains; it does not equate the new values with their source variables.
See the [official integer-variable specification](https://xcsp.org/specifications/variables/integer/).

`example.xml` is an upstream syntax showcase rather than a valid core instance:
it declares `type="CSP"` but contains an `<objectives>` section, and later uses
an array id as the scalar operand of `add`. The strict frontend now rejects the
framework mismatch before reaching that ill-typed expression.

`obj.xml` refuses on `ne(sub(x[1],x[2]))`, a unary `ne`. XCSP3 has no such
operator: the [official expression grammar](https://xcsp.org/specifications/syntax/)
requires two integer expressions for `ne`. The refusal is retained.
