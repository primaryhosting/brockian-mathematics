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

lemma rpow_pow_comm (b : ℝ) (hb : 0 < b) (t : ℝ) (k : ℕ) :
    ((b ^ k : ℝ)) ^ t = ((b : ℝ) ^ t) ^ k := by
  rw [← Real.rpow_natCast b k, ← Real.rpow_natCast (b ^ t) k, ← Real.rpow_mul hb.le,
    ← Real.rpow_mul hb.le, mul_comm]

/-- `(b^k)^(log_b a) = a^k`. -/
