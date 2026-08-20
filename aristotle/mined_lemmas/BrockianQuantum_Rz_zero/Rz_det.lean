import Mathlib
/-!
# Batch 15 — single-qubit Z-rotations Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2}) in SU(2). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem Rz_det (t : ℝ) : (Rz t).det = 1 := by
  simp [Rz, Matrix.det_fin_two_of, ← Complex.exp_add]
  ring_nf
  simp

