import Mathlib
open Matrix Polynomial
namespace C5.BSp6

def P10 : Matrix (Fin 10) (Fin 10) ℝ := Matrix.of (fun i j => if i=j then 2 else if (i:ℤ)-(j:ℤ)=1 ∨ (j:ℤ)-(i:ℤ)=1 then -1 else 0)

