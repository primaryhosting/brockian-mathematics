/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Real

/-- `((b:ℝ)^k) ^ t = (b ^ t) ^ k` for `b > 0`, natural `k`, real exponent `t`. -/

lemma pow_rpow_logb (a b : ℝ) (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a) = a ^ k := by
  rw [rpow_pow_comm b (lt_trans zero_lt_one hb) _ k,
    Real.rpow_logb (lt_trans zero_lt_one hb) (ne_of_gt hb) ha]

/-- `(b^k)^(log_b a - ε) = a^k * (b^(-ε))^k`. -/
