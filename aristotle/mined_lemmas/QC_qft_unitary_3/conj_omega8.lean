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

set_option grind.warning false

namespace QC

open Complex

/-- The primitive 8-th root of unity `exp(2πi/8)`. -/

lemma conj_omega8 : (starRingEnd ℂ) omega8 = omega8 ^ 7 := by
  have h : omega8 * omega8 ^ 7 = 1 := by
    rw [← pow_succ']
    exact omega8_pow_eight
  have hinv : omega8⁻¹ = (starRingEnd ℂ) omega8 := Complex.inv_eq_conj norm_omega8
  rw [← hinv]
  exact inv_eq_of_mul_eq_one_right h

/-- Sum of the 8-th roots of unity along an arithmetic progression of exponents. -/
