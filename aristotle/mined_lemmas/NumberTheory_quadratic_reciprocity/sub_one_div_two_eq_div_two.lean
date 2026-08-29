import Mathlib
/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- For an odd natural number `p`, the expressions `(p - 1) / 2` and `p / 2` agree
(natural-number division). -/

lemma sub_one_div_two_eq_div_two {p : ℕ} (hp : p % 2 = 1) : (p - 1) / 2 = p / 2 := by
  omega

/-- **Gauss's Law of Quadratic Reciprocity**: for distinct odd primes `p` and `q`,
`(p / q) * (q / p) = (-1) ^ ((p-1)/2 * (q-1)/2)`, where `(· / ·)` denotes the
Legendre symbol. -/
