import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem T_unitary : T * Tᴴ = 1 := by
  have h : Complex.exp (Complex.I * Real.pi / 4) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have e : Complex.I * (Real.pi : ℂ) / 4
        + (starRingEnd ℂ) (Complex.I * (Real.pi : ℂ) / 4) = 0 := by
      rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring
    rw [e, Complex.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_two, h]

