import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex ZMod AddChar Matrix Finset

/-- The `N`-dimensional quantum Fourier transform matrix: the entry in row `j`, column `k` is
`exp (2 π i · j · k / N) / √N`, with rows and columns indexed by `ZMod N`. -/

lemma sum_stdAddChar_mul (N : ℕ) [NeZero N] (t : ZMod N) :
    ∑ m : ZMod N, stdAddChar (m * t) = if t = 0 then (N : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift t (isPrimitive_stdAddChar N)]
  simp [ZMod.card]

/-- The `N`-dimensional quantum Fourier transform matrix is unitary. -/
