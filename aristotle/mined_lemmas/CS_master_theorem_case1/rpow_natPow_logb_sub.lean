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

set_option grind.warning false

namespace CS

/-- `(b^k)^(log_b a) = a^k`. -/

lemma rpow_natPow_logb_sub (a : ℝ) (b : ℕ) (eps : ℝ) (hb : 2 ≤ b) (ha : 0 < a) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (Real.logb b a - eps) = a ^ k * ((b : ℝ) ^ (-eps)) ^ k := by
  have hb0 : (0:ℝ) < (b:ℝ) := by
    have : (0:ℕ) < b := by omega
    exact_mod_cast this
  have hb1 : (b:ℝ) ≠ 1 := by
    have : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    linarith
  rw [← Real.rpow_natCast (b:ℝ) k, ← Real.rpow_mul hb0.le, mul_comm, Real.rpow_mul hb0.le,
    Real.rpow_sub hb0, Real.rpow_logb hb0 hb1 ha, Real.rpow_natCast, ← mul_pow]
  congr 1
  rw [Real.rpow_neg hb0.le, div_eq_mul_inv]

/-- Geometric series bound. -/
