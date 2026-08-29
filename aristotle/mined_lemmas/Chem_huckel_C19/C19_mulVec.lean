/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/

lemma C19_mulVec (v : ZMod 19 → ℂ) (i : ZMod 19) :
    C19.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 19) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 19) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have key : ∀ j : ZMod 19, (if i - j = 1 ∨ j - i = 1 then (1 : ℂ) else 0) * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ (j = i - 1) := by
      constructor <;> intro h <;> linear_combination -h
    have h2 : (j - i = 1) ↔ (j = i + 1) := by
      constructor <;> intro h <;> linear_combination h
    by_cases hA : j = i - 1
    · have hB : j ≠ i + 1 := by rw [hA]; exact hne
      simp [hA, hne]
    · by_cases hB : j = i + 1
      · simp [hB, Ne.symm hne]
      · simp [h1, h2, hA, hB]
  simp only [Matrix.mulVec, dotProduct, C19]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib]
  simp

/-- For each `x : ZMod 19`, the vector `j ↦ ζ^(jx)` is an eigenvector of the adjacency matrix
of `C₁₉` with eigenvalue `2 cos (2π x /19)`. -/
