import Mathlib
-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the required header comment appears immediately below the import.)

/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- For an odd natural number `n`, `(n - 1) / 2 = n / 2` (natural subtraction and division). -/

theorem odd_nat_pred_div_two (n : ℕ) (hn : Odd n) : (n - 1) / 2 = n / 2 := by
  obtain ⟨k, rfl⟩ := hn
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
