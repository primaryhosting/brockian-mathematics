import Mathlib
open Matrix

namespace C3.Alg4

/-- Chinese Remainder Theorem: for coprime `m` and `n`, `ZMod (m*n)` is isomorphic
as a ring to `ZMod m × ZMod n`. -/

theorem det_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Aᵀ.det = A.det :=
  Matrix.det_transpose A

end C3.Alg4

