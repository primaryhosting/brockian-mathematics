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

lemma f_pow_bound (ha : 0 < a) (hb : 2 ≤ b)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ C * (n : ℝ) ^ (Real.logb b a - e)) (k : ℕ) :
    f (b ^ k) ≤ C * a ^ k * ((b : ℝ) ^ (-e)) ^ k := by
  have hb1 : (1 : ℝ) < (b : ℕ) := by exact_mod_cast hb.trans_lt' one_lt_two
  have hbk : 1 ≤ b ^ k := Nat.one_le_pow _ _ (by omega)
  have := hf (b ^ k) hbk
  have hcast : ((b ^ k : ℕ) : ℝ) = ((b : ℝ)) ^ k := by push_cast; ring
  rw [hcast] at this
  have hsplit : ((b : ℝ) ^ k) ^ (Real.logb b a - e)
      = a ^ k * ((b : ℝ) ^ (-e)) ^ k := by
    have hbk0 : (0 : ℝ) < (b : ℝ) ^ k := pow_pos (lt_trans zero_lt_one hb1) k
    rw [sub_eq_add_neg, Real.rpow_add hbk0, rpow_logb_pow ha hb1 k, rpow_neg_pow hb1 e k]
  rw [hsplit] at this
  linarith [this]

/-- Lower bound: `a^k * T 1 ≤ T (b^k)`. -/
