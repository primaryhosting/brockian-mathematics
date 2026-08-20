import Mathlib
open Matrix Polynomial
namespace C6.BSp7


def C8 : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of (fun i j => if ((i:ℤ)-(j:ℤ))%8=1 ∨ ((j:ℤ)-(i:ℤ))%8=1 then 1 else 0)

/-- The cycle adjacency matrix has zero diagonal, hence zero trace. -/
