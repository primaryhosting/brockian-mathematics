import Mathlib

/-!
# Pell 8 — companion results

Supplementary development for the target theorem `Math.pell_8`
(`RequestProject/Pell8.lean`): the Pell equation `x² - 8·y² = 1` has not merely one
nontrivial integer solution, but infinitely many, generated from `(3, 1)` by the
automorphism `(x, y) ↦ (3x + 8y, x + 3y)` of the form `x² - 8y²`.
-/

namespace Math

/-- One application of the Pell automorphism attached to the fundamental
solution `(3, 1)` of `x² - 8y² = 1`. -/

theorem pell_8_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 8 * y ^ 2 = 1 ∧ N < y := by
  refine ⟨(pellSol N.toNat).1, (pellSol N.toNat).2, pellSol_form _, ?_⟩
  have h := pellSol_snd_ge N.toNat
  have : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  linarith

/-- The set of nontrivial integer solutions of `x² - 8·y² = 1` is infinite. -/
