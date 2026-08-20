import Mathlib
open Matrix Polynomial
namespace C6.BSp7


theorem P11_symm : P11.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, P11, Matrix.of_apply]
  rcases eq_or_ne i j with h | h
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]
    congr 1
    exact propext (by tauto)

/-- `2` is an eigenvalue of `P11`: the matrix `2 • 1 - P11` is the adjacency matrix of the
path on 11 vertices, which kills the alternating vector `(1,0,-1,0,1,0,-1,0,1,0,-1)`. -/
