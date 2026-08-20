import Mathlib
namespace C2.Alg3

/-- Cramer-style solution: if `det A` is a unit, then `A⁻¹ b` solves `A x = b`. -/

theorem adjugate_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : A * A.adjugate = A.det • 1 :=
  Matrix.mul_adjugate A

/-- Sylow's existence theorem: a finite group has a Sylow `p`-subgroup. -/
