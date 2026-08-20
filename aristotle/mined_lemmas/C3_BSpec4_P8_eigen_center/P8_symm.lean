import Mathlib
open Matrix Polynomial
namespace C3.BSpec4

theorem P8_symm : P8.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, P8, Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
    congr 1
    exact propext or_comm

