import Mathlib
open Matrix Polynomial
namespace C4.BSp5

def P9 : Matrix (Fin 9) (Fin 9) ℝ := Matrix.of (fun i j => if i=j then 2 else if (i:ℤ)-(j:ℤ)=1 ∨ (j:ℤ)-(i:ℤ)=1 then -1 else 0)

/-- `2` is an eigenvalue of the `9 × 9` path Laplacian-type matrix `P9`: the matrix
`2 • 1 - P9` kills the nonzero vector `(1,0,-1,0,1,0,-1,0,1)`, hence has zero
determinant, which by `Matrix.eval_charpoly` is `P9.charpoly.eval 2`. -/
