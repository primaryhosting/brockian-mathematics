import Mathlib
/-!
# Batch 8 — discrete/quantum Fourier transform (concrete 2- and 4-point). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
/-- 2-point DFT (unnormalized) = √2 · Hadamard. -/

theorem W2_unitary : W2 * W2ᴴ = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> norm_num
