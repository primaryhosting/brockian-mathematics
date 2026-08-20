/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`p` is at least `2` and its only divisors are `1` and `p`. -/

theorem isPrimeNat_of_prime {p : ℕ} (hp : p.Prime) : IsPrimeNat p :=
  ⟨hp.two_le, fun d hd => (Nat.Prime.eq_one_or_self_of_dvd hp d hd)⟩

/-- Admissibility of the `4`-tuple `(0, 2, 6, 8)`, phrased with `ZMod p`:
for every prime `p` there is a residue class in `ZMod p` hit by none of the shifts. -/
