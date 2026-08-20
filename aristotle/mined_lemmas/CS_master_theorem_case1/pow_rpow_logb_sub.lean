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

lemma pow_rpow_logb_sub (a b : ℝ) (ha : 0 < a) (hb : 1 < b) (e : ℝ) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a - e) = a ^ k * ((b : ℝ) ^ (-e)) ^ k := by
  have hb0 : (0:ℝ) < b := lt_trans zero_lt_one hb
  rw [rpow_pow_comm b hb0 _ k, ← mul_pow]
  congr 1
  rw [show Real.logb b a - e = Real.logb b a + (-e) by ring, Real.rpow_add hb0,
    Real.rpow_logb hb0 (ne_of_gt hb) ha]

/-- **Master theorem, case 1.**

Let `T` satisfy the divide-and-conquer recurrence `T n = a * T (n / b) + f n`, stated on the
powers of `b` (the standard domain on which the master theorem is proved):
`T (b^(k+1)) = a * T (b^k) + f (b^(k+1))`.  Assume `f` is nonnegative and
`f n = O (n ^ (log_b a - ε))` for some `ε > 0`, in the explicit form `f n ≤ C * n ^ (log_b a - ε)`.
Then `T (b^k) = Θ ((b^k) ^ (log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * (b^k)^(log_b a) ≤ T (b^k) ≤ c₂ * (b^k)^(log_b a)` for all `k`.

Mathlib has no master theorem as such; the nearest existing machinery is the Akra–Bazzi theorem
(`Mathlib/Computability/AkraBazzi/AkraBazzi.lean`, `AkraBazziRecurrence`), which is stated for a
different (floor/ceiling based, smoothness-constrained) setup and does not close this statement.
The proof below is the standard geometric-series estimate on the recursion tree; the only
nontrivial library input is `Real.rpow_logb` (`b ^ logb b a = a`). -/
