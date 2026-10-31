// `call forall` invokes a lemma procedure -- no out-parameters, no checked
// modifies -- and means `assume (forall <wildcards> :: Pre ==> Post)`
// (This is Boogie 2 §9.10). The wildcard call quantifies; the second call
// supplies the argument and assumes the instantiated implication directly.

procedure Lemma(x: int);
  requires x >= 0;
  ensures  x + 1 > x;

procedure P(a: int) returns (r: int)
  requires a >= 0;
  ensures  r > a;
{
  call forall Lemma(*);
  call forall Lemma(a);
  r := a + 1;
}
