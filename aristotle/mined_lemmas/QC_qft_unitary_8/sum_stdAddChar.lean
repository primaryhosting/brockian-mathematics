/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex Real ZMod AddChar

namespace QC

/-- The `N × N` quantum Fourier transform matrix, indexed by `ZMod N`:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`. -/

lemma sum_stdAddChar (N : ℕ) [NeZero N] (t : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (k * t) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · simpa [AddChar.mulShift_apply, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- The `N`-dimensional quantum Fourier transform matrix is unitary. -/
