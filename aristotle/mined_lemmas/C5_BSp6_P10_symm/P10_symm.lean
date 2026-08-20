import Mathlib
open Matrix Polynomial
namespace C5.BSp6

theorem P10_symm : P10.IsSymm := by
  ext i j
  simp only [P10, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases h2 : (i:ℤ)-(j:ℤ)=1 ∨ (j:ℤ)-(i:ℤ)=1
    · rw [if_pos h2, if_pos h2.symm]
    · rw [if_neg h2, if_neg (fun h3 => h2 h3.symm)]

/-- The eigenvector of `P10` for the eigenvalue `2 - 2 cos (π/11)`:
its `i`-th entry is `sin ((i+1) π / 11)`. -/
