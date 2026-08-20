import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

/-- `omega` is the primitive 8th root of unity `exp (2πi/8)` used by the 3-qubit QFT. -/

lemma conj_omega : (starRingEnd ℂ) omega = omega⁻¹ := by
  rw [omega, ← Complex.inv_eq_conj]
  simp [Complex.norm_exp]

/-- Orthogonality of the columns of the (unnormalized) QFT matrix. -/
