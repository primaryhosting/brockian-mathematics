import Mathlib
/-!
# Batch 8 — discrete/quantum Fourier transform (concrete 2- and 4-point). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
/-- 2-point DFT (unnormalized) = √2 · Hadamard. -/

theorem W4_symmetric : W4ᵀ = W4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W4, Matrix.transpose_apply]
