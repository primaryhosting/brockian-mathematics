/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Real

/-- Auxiliary: `((b : ℝ) ^ k) ^ (t : ℝ) = ((b : ℝ) ^ (t : ℝ)) ^ k` (rpow of a natural power). -/

lemma rpow_natPow (b : ℝ) (hb : 0 < b) (k : ℕ) (t : ℝ) :
    (b ^ k) ^ t = (b ^ t) ^ k := by
  rw [← Real.rpow_natCast b k, ← Real.rpow_natCast (b ^ t) k, ← Real.rpow_mul hb.le,
    ← Real.rpow_mul hb.le, mul_comm]

/-- `((b : ℝ) ^ k) ^ (log_b a) = a ^ k`, the "critical exponent" evaluated at `n = b ^ k`. -/
