import Mathlib
open Matrix Polynomial
namespace C3.BSpec4

def P8 : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of (fun i j => if i=j then 2 else if (i:ℤ)-(j:ℤ)=1 ∨ (j:ℤ)-(i:ℤ)=1 then -1 else 0)

/-- The eigenvector of `P8` for the eigenvalue `2 - 2 cos (π/9)`:
its `i`-th entry is `sin ((i+1) π/9)`. -/
