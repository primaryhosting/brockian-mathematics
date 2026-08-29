/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This module is deliberately import-free (Lean forbids `import` after the header
-- comment above), so primality is spelled out from first principles here.  The
-- companion module `RequestProject.GoldbachWheelK2_1327Mathlib` proves that
-- `Brockian.IsPrimeNat` coincides with Mathlib's `Nat.Prime`, and restates the
-- main theorem in Mathlib's vocabulary.

namespace Brockian

set_option maxRecDepth 100000

/-- Primality, from first principles: `n` is at least `2` and its only divisors are
`1` and `n`. -/

theorem no_small_divisor {n : Nat} (h : trialAux n n 2 = true) :
    ∀ e, 2 ≤ e → e * e ≤ n → ¬ e ∣ n := by
  intro e he hen
  have hen' : e ≤ n := Nat.le_trans (Nat.le_mul_of_pos_left e (by omega)) hen
  exact trialAux_spec n n 2 h e he hen (by omega)

