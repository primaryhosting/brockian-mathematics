/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- `((b:ℝ)^k) ^ (log_b a + t) = a^k * (b^t)^k` (real powers).
Specializing `t = 0` gives `(b^k)^{log_b a} = a^k`, i.e. `n^{log_b a} = a^k` for `n = b^k`. -/

private lemma rpow_pow_logb_add (a : ℝ) (b : ℕ) (ha : 0 < a) (hb : 2 ≤ b) (k : ℕ) (t : ℝ) :
    (((b : ℝ) ^ k)) ^ (Real.logb b a + t) = a ^ k * (((b : ℝ) ^ t) ^ k) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hbl : (b : ℝ) ^ (Real.logb b a) = a := Real.rpow_logb hb0 (by linarith) ha
  rw [← Real.rpow_natCast (b : ℝ) k, ← Real.rpow_mul hb0.le, mul_comm, Real.rpow_mul hb0.le,
    Real.rpow_natCast, Real.rpow_add hb0, hbl, mul_pow]

/-- Partial sums of a geometric series with ratio in `[0,1)` are bounded by `(1-r)⁻¹`. -/
