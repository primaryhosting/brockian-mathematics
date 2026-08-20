import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem T_sq_eq_S : T * T = S := by
  have h : Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)
      = Complex.I := by
    rw [← Complex.exp_add]
    have e : Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
        = (Real.pi / 2 : ℝ) * Complex.I := by push_cast; ring
    rw [e, Complex.exp_mul_I]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, S, Matrix.mul_apply, Fin.sum_univ_two, h]

