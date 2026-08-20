import Mathlib
namespace Brockian.StarOfDavid

/-- `(a+b).choose a * a! * b! = (a+b)!`. -/

private lemma star_abstract {a b c a' b' c' : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0)
    (hprod : a * b * c = a' * b' * c')
    (h1 : c' = a + a' + b) (h2 : c = b' + a + a') :
    Nat.gcd (Nat.gcd a b) c = Nat.gcd (Nat.gcd a' b') c' :=
  Nat.dvd_antisymm (star_key ha hb hc ha' hb' hc' hprod h1 h2)
    (star_key ha' hb' hc' ha hb hc hprod.symm (by omega) (by omega))

/-- The Star of David theorem: the two alternating triples of binomial coefficients surrounding
    an entry of Pascal's triangle have equal gcd. -/
