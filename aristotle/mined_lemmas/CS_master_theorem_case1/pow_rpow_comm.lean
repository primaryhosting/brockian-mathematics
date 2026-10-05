import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- Commuting a natural power with a real power: `(b ^ k) ^ c = (b ^ c) ^ k`. -/

lemma pow_rpow_comm {b : ℝ} (hb : 0 ≤ b) (c : ℝ) (k : ℕ) :
    ((b ^ k : ℝ)) ^ c = ((b : ℝ) ^ c) ^ k := by
  rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb, mul_comm, Real.rpow_mul hb,
    Real.rpow_natCast]

/-- On the points `n = b ^ k`, the function `n ↦ n ^ (log_b a)` is `a ^ k`. -/
