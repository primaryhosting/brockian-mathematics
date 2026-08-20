import Mathlib

/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- For an odd prime `p`, `(p - 1) / 2 = p / 2` (natural number division/subtraction). -/

lemma pred_div_two_eq_div_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (p - 1) / 2 = p / 2 := by
  have hp₁ : p % 2 = 1 :=
    (Nat.Prime.eq_two_or_odd <| @Fact.out (Nat.Prime p) _).resolve_left hp
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
