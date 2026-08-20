import Mathlib
open Matrix Polynomial
namespace C4.BSp5

theorem P9_symm : P9.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, P9, Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), if_congr or_comm rfl rfl]

