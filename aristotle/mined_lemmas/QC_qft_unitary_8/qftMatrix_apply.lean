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

lemma qftMatrix_apply (N : ℕ) [NeZero N] (j k : ZMod N) :
    qftMatrix N j k = (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (j * k) := by
  have h : ((j.val * k.val : ℕ) : ZMod N) = j * k := by push_cast [ZMod.natCast_val]; simp
  rw [qftMatrix]
  simp only [Matrix.of_apply]
  rw [div_eq_inv_mul, ← h,
    show ((j.val * k.val : ℕ) : ZMod N) = (((j.val * k.val : ℕ) : ℤ) : ZMod N) by push_cast; ring,
    ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- Complex conjugation inverts the standard additive character. -/
