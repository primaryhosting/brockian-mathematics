import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- For `b > 0`, taking the `k`-th (natural) power commutes with the real power `c`. -/

lemma pow_rpow_logb {a b : ℝ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a) = a ^ k := by
  rw [pow_rpow_comm (lt_trans zero_lt_one hb), Real.rpow_logb (lt_trans zero_lt_one hb)
    (ne_of_gt hb) ha]

/-- The geometric sum bound `∑_{j<n} q^j ≤ (1-q)⁻¹` for `0 ≤ q < 1`. -/
