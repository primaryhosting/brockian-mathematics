import Mathlib
/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- For an odd prime `p`, the natural-number expression `(p - 1) / 2` (truncated
subtraction and division) equals `p / 2`. -/

theorem odd_prime_sub_one_div_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p - 1) / 2 = p / 2 := by
  have h := (Nat.Prime.eq_two_or_odd hp).resolve_left hp2
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
