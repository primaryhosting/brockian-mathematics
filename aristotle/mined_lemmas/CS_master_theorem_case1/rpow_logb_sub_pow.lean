import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Commuting a natural power with a real power: `(b ^ k) ^ c = (b ^ c) ^ k`. -/

lemma rpow_logb_sub_pow {a b eps : ℝ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ((b ^ k : ℝ)) ^ (Real.logb b a - eps) = a ^ k * ((b : ℝ) ^ (-eps)) ^ k := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  rw [pow_rpow_comm hb0.le, ← mul_pow]
  congr 1
  rw [sub_eq_add_neg, Real.rpow_add hb0, Real.rpow_logb hb0 hb.ne' ha]

/-- **Master theorem, Case 1** (on the exact powers of `b`).

Let `T` satisfy the divide-and-conquer recurrence `T(n) = a·T(n/b) + f(n)`, written here
along the powers of `b`: `T k` stands for `T (b ^ k)` and `f k` for `f (b ^ k)`, so the
recurrence reads `T (k+1) = a * T k + f (k+1)`.

Assume `a ≥ 1`, `b > 1`, the driving function `f` is nonnegative and satisfies the
`O(n ^ (log_b a - ε))` bound `f (b ^ k) ≤ C * (b ^ k) ^ (log_b a - ε)` with `ε > 0`, and
`T (b ^ 0) > 0`.

Then `T (b ^ k) = Θ((b ^ k) ^ (log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * n ^ (log_b a) ≤ T n ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`. -/
