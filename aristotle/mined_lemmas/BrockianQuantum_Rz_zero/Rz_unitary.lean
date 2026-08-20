import Mathlib
/-!
# Batch 15 — single-qubit Z-rotations Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2}) in SU(2). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem Rz_unitary (t : ℝ) : Rz t * (Rz t)ᴴ = 1 := by
  rw [Rz_conj, Rz_add]
  simp [Rz_zero]

