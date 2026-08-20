import Mathlib
namespace C2.Alg3

/-- Cramer-style solution: if `det A` is a unit, then `A⁻¹ b` solves `A x = b`. -/

theorem cramer_solve {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (b : Fin n → ℝ) :
    A.mulVec (A⁻¹.mulVec b) = b := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]

/-- The adjugate identity `A * adj A = det A • 1`. -/
