import Mathlib
open Matrix
namespace C4.QC6

theorem T_sq_eq_S : T * T = S := by
  have h : Complex.exp (Complex.I*Real.pi/4) * Complex.exp (Complex.I*Real.pi/4)
      = Complex.I := by
    rw [← Complex.exp_add]
    have h2 : Complex.I*(Real.pi:ℂ)/4 + Complex.I*(Real.pi:ℂ)/4
        = ((Real.pi/2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2, Complex.exp_mul_I]
    simp
  rw [T, S, Matrix.mul_fin_two]
  simp [h]

