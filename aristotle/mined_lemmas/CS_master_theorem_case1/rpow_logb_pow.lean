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

Case 1 of the Master Theorem for divide-and-conquer recurrences:
if `T(n) = a * T(n/b) + f(n)` with `f(n) = O(n^(log_b a - ε))` for some `ε > 0`,
then `T(n) = Θ(n^(log_b a))`.

As usual for the Master Theorem, the recurrence is analysed along the powers of `b`,
i.e. we write `T k` for the value of the recurrence at `n = b ^ k`.
-/

namespace CS

/-- At `n = b ^ k`, the driving function `n ^ (log_b a)` equals `a ^ k`. -/

theorem rpow_logb_pow (a b : ℝ) (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b : ℝ) ^ k) ^ Real.logb b a = a ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_logb hb0 (ne_of_gt hb) ha, Real.rpow_natCast]

/-- At `n = b ^ k`, we have `n ^ (log_b a - ε) = a ^ k / (b ^ ε) ^ k`. -/
