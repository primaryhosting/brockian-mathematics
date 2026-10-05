/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma adj_row_sum (f : ZMod 20 → ℂ) (i : ZMod 20) :
    ∑ j, adjC20 i j * f j = f (i - 1) + f (i + 1) := by
  have hne : (i - 1 : ZMod 20) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 20) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j, adjC20 i j * f j
      = (if j = i - 1 then f j else 0) + (if j = i + 1 then f j else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ j = i - 1 := by
      constructor <;> intro h <;> linear_combination -h
    have h2 : (j - i = 1) ↔ j = i + 1 := by
      constructor <;> intro h <;> linear_combination h
    simp only [adjC20, Matrix.of_apply, h1, h2]
    by_cases hA : j = i - 1 <;> by_cases hB : j = i + 1 <;>
      simp_all
  simp only [key, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (i - 1) f, Finset.sum_ite_eq' Finset.univ (i + 1) f]
  simp

