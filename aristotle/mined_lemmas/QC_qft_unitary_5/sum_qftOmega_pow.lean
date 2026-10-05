/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

open Complex Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma sum_qftOmega_pow (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    ∑ l ∈ Finset.range n, qftOmega n ^ (l * m) = if n ∣ m then (n : ℂ) else 0 := by
  have hx : ∀ l : ℕ, qftOmega n ^ (l * m) = (qftOmega n ^ m) ^ l := by
    intro l; rw [← pow_mul, Nat.mul_comm]
  simp only [hx]
  by_cases h : n ∣ m
  · have h1 : qftOmega n ^ m = 1 := (qftOmega_pow_eq_one_iff n hn m).mpr h
    simp [h1, h]
  · have h1 : qftOmega n ^ m ≠ 1 := fun hc =>
      h ((qftOmega_pow_eq_one_iff n hn m).mp hc)
    have h2 : (qftOmega n ^ m) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, qftOmega_pow_n n hn, one_pow]
    rw [geom_sum_eq h1, h2]
    simp [h]

