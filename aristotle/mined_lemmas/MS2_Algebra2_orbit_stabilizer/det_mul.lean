import Mathlib
namespace MS2.Algebra2

theorem det_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : (A*B).det = A.det * B.det :=
  Matrix.det_mul A B
