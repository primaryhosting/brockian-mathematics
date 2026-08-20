import Mathlib
/-!
# Batch 15 — single-qubit Z-rotations Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2}) in SU(2). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem Rz_two_pi : Rz (2 * Real.pi) = -1 := by
  have h1 : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm]; exact Complex.exp_pi_mul_I
  have h2 : Complex.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
    rw [Complex.exp_neg, h1]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz] <;> ring_nf <;> simp [h1, h2]

