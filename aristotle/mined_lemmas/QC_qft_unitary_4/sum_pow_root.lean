import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

/-- The primitive 16-th root of unity `exp (2πi/16)`. -/

lemma sum_pow_root (x : ℂ) (hx : x ^ (16 : ℕ) = 1) :
    ∑ k : Fin 16, x ^ (k : ℕ) = if x = 1 then 16 else 0 := by
  by_cases h : x = 1
  · simp [h]
  · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun i => x ^ i) 16, geom_sum_eq h, hx]
    simp

