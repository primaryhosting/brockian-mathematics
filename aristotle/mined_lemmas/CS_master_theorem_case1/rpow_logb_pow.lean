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

lemma rpow_logb_pow {a b : ℝ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a) = a ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  rw [pow_rpow_comm hb0.le, Real.rpow_logb hb0 hb.ne' ha]

/-- On the points `n = b ^ k`, the function `n ↦ n ^ (log_b a - ε)` equals
`a ^ k * r ^ k` where `r = b ^ (-ε) < 1`. -/
