/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- A primitive 8-th root of unity, `exp (2πi/8)`. -/

lemma conj_zeta8 : (starRingEnd ℂ) zeta8 = zeta8⁻¹ := by
  have h : ‖zeta8‖ = 1 := by
    simp [zeta8, Complex.norm_exp]
  rw [← Complex.inv_eq_conj h]

