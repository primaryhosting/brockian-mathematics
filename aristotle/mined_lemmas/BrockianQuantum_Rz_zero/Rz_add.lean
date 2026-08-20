import Mathlib
/-!
# Batch 15 — single-qubit Z-rotations Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2}) in SU(2). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem Rz_add (s t : ℝ) : Rz s * Rz t = Rz (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz, Matrix.mul_apply, Fin.sum_univ_succ, ← Complex.exp_add] <;> ring_nf

