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

lemma conj_stdAddChar (N : ℕ) [NeZero N] (x : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.starComp_apply (by simp [ZMod.ringChar_zmod_n, Nat.pos_of_neZero]), AddChar.inv_apply]

/-- Orthogonality relation: the character sum `∑ k, ζ^(k t)` is `N` if `t = 0` and `0` otherwise. -/
