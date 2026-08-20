/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex

namespace QC

/-- The primitive `2^7 = 128`-th root of unity `exp (2πi/128)`. -/

theorem qft_unitary_7 : qft7 ∈ Matrix.unitaryGroup (Fin 128) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin 128, (star qft7) a k * qft7 k b
      = (1 / 128 : ℂ) *
        ((starRingEnd ℂ) (qftOmega ^ (k.val * a.val)) * qftOmega ^ (k.val * b.val)) := by
    intro k
    rw [Matrix.star_apply]
    show (starRingEnd ℂ) (qft7 k a) * qft7 k b = _
    rw [qft7]
    simp only [Matrix.of_apply, map_mul, Complex.conj_ofReal]
    rw [← qft_norm_sq]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, qft_sum]
  by_cases h : a = b
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h, mul_zero]

end QC

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

