import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F j k = exp (2 π i j k / N) / √N`. -/

lemma dftMatrix_apply (N : ℕ) (j k : Fin N) :
    dftMatrix N j k = omegaN N ^ (j.val * k.val) / Real.sqrt N := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) * (k.val : ℂ)) / (N : ℂ))
      = ((j.val * k.val : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) := by
    push_cast
    ring
  rw [dftMatrix, omegaN, ← Complex.exp_nat_mul, ← harg]

