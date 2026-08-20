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

theorem rpow_logb_sub_pow (a b ε : ℝ) (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b : ℝ) ^ k) ^ (Real.logb b a - ε) = a ^ k / ((b : ℝ) ^ ε) ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hbk : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hb0 k
  rw [Real.rpow_sub hbk, rpow_logb_pow a b ha hb k]
  congr 1
  rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb0.le, mul_comm,
    Real.rpow_mul hb0.le, Real.rpow_natCast]

/-- **Master Theorem, Case 1.**  Consider a divide-and-conquer recurrence
`T(n) = a * T(n / b) + f(n)` with `a ≥ 1`, `b > 1`, driving function `f ≥ 0`
satisfying `f(x) ≤ C * x ^ (log_b a - ε)` for some `ε > 0` (i.e. `f(n) = O(n^(log_b a - ε))`).
Then `T(n) = Θ(n ^ (log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * n ^ (log_b a) ≤ T(n) ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`.
Here `T k` denotes the value of the recurrence at `n = b ^ k`. -/
