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

/-- `((b:ℝ)^k) ^ (log_b a) = a ^ k` (outer exponent is a real power). -/

lemma rpow_neg_pow {b : ℝ} (hb : 1 < b) (e : ℝ) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (-e) = ((b : ℝ) ^ (-e)) ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  rw [← Real.rpow_natCast (b : ℝ) k, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_natCast]

section

variable {a e C : ℝ} {b : ℕ} {T f : ℕ → ℝ}

/-- Under the case-1 hypotheses, `f (b^k) ≤ C * a^k * r^k` where `r = b^(-ε)`. -/
