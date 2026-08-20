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

lemma sum_omega8_pow (d : ℕ) :
    ∑ k ∈ Finset.range 8, (omega8 ^ d) ^ k = if 8 ∣ d then 8 else 0 := by
  by_cases hd : 8 ∣ d
  · have h1 : omega8 ^ d = 1 := (isPrimitiveRoot_omega8.pow_eq_one_iff_dvd d).2 hd
    simp [h1, hd]
  · have h1 : omega8 ^ d ≠ 1 := fun h =>
      hd ((isPrimitiveRoot_omega8.pow_eq_one_iff_dvd d).1 h)
    have h8 : (omega8 ^ d) ^ 8 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, omega8_pow_eight, one_pow]
    rw [geom_sum_eq h1 8, h8, if_neg hd]
    simp

