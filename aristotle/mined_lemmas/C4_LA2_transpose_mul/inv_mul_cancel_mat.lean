import Mathlib
namespace C4.LA2
open Matrix

theorem inv_mul_cancel_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit A.det) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A h
end C4.LA2

