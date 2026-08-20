import Mathlib
open Matrix Polynomial
namespace C6.BSp7


def P11 : Matrix (Fin 11) (Fin 11) ℝ := Matrix.of (fun i j => if i=j then 2 else if (i:ℤ)-(j:ℤ)=1∨(j:ℤ)-(i:ℤ)=1 then -1 else 0)

/-- The path Laplacian-type matrix `P11` is symmetric. -/
