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

lemma geom_sum_zeta8 {d : ℕ} (hd : ¬ (8 ∣ d)) :
    ∑ l ∈ Finset.range 8, (zeta8 ^ d) ^ l = 0 := by
  rw [geom_sum_eq (zeta8_pow_ne_one hd)]
  have : (zeta8 ^ d) ^ 8 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta8_pow_eight, one_pow]
  rw [this]
  simp

/-- Rows of `qft3` are orthonormal. -/
