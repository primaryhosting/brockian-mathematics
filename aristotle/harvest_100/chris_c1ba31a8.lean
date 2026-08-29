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

/-
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-! ## Setup

Throughout, `k p m : ℕ` and `m` is a *Thabit-form* number `m = (2 ^ k - 1) * (p + 2)`.
Both this shape and the divisor-sum criterion that accompanies it are stated in a
**subtraction-free** way, so that no truncated natural subtraction can ever occur:

* `IsThabitForm k p m : m + (p + 2) = 2 ^ k * (p + 2)` says `m = (2 ^ k - 1) * (p + 2)`;
* `SigmaCriterion k p m : σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)` says
  `σ m = (2 ^ (k + 1) - 1) * (p + 1)`.

Under these two hypotheses the *balance identity*

`σ m + 2 ^ (k + 1) = 2 * m + (p + 3)`

holds, and it immediately converts the deficient / perfect / abundant trichotomy for `m`
into a comparison between `p + 3` and `2 ^ (k + 1)`.
-/

/-- `m` has *Thabit form* with parameters `k`, `p`, i.e. `m = (2 ^ k - 1) * (p + 2)`,
written subtraction-freely. -/
def IsThabitForm (k p m : ℕ) : Prop := m + (p + 2) = 2 ^ k * (p + 2)

/-- The *sigma criterion*: `σ m = (2 ^ (k + 1) - 1) * (p + 1)`, written subtraction-freely. -/
def SigmaCriterion (k p m : ℕ) : Prop := σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)

/-! ## The balance identity -/

/-- **Thabit balance identity.**  If `m = (2 ^ k - 1) * (p + 2)` and `m` satisfies the
sigma criterion `σ m = (2 ^ (k + 1) - 1) * (p + 1)`, then

`σ m + 2 ^ (k + 1) = 2 * m + (p + 3)`.

Everything is stated over `ℕ` without any subtraction. -/
theorem thabit_balance_identity {k p m : ℕ} (hm : IsThabitForm k p m)
    (hs : SigmaCriterion k p m) :
    σ 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  unfold IsThabitForm at hm
  unfold SigmaCriterion at hs
  rw [pow_succ] at hs ⊢
  -- both hypotheses and the goal are linear in the atoms `m`, `p`, `σ 1 m`, `2 ^ k`, `2 ^ k * p`
  zify at hm hs ⊢
  linear_combination hs - 2 * hm

/-! ## Deficient / perfect / abundant comparisons -/

/-- Rewriting the balance identity: the divisor sum of `m` compared with `2 * m` is governed
by the comparison of `p + 3` with `2 ^ (k + 1)`. -/
theorem sum_properDivisors_balance {k p m : ℕ} (hm : IsThabitForm k p m)
    (hs : SigmaCriterion k p m) :
    (∑ i ∈ m.properDivisors, i) + m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  have h := thabit_balance_identity hm hs
  rwa [ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self] at h

/-- A Thabit-form number satisfying the sigma criterion is **deficient** exactly when
`p + 3 < 2 ^ (k + 1)`. -/
theorem thabit_deficient_iff {k p m : ℕ} (hm : IsThabitForm k p m)
    (hs : SigmaCriterion k p m) :
    m.Deficient ↔ p + 3 < 2 ^ (k + 1) := by
  have h := sum_properDivisors_balance hm hs
  unfold Nat.Deficient
  omega

/-- A Thabit-form number satisfying the sigma criterion is **perfect** exactly when
`p + 3 = 2 ^ (k + 1)` (and `m` is positive). -/
theorem thabit_perfect_iff {k p m : ℕ} (hm : IsThabitForm k p m)
    (hs : SigmaCriterion k p m) (hpos : 0 < m) :
    m.Perfect ↔ p + 3 = 2 ^ (k + 1) := by
  have h := sum_properDivisors_balance hm hs
  unfold Nat.Perfect
  omega

/-- A Thabit-form number satisfying the sigma criterion is **abundant** exactly when
`2 ^ (k + 1) < p + 3`. -/
theorem thabit_abundant_iff {k p m : ℕ} (hm : IsThabitForm k p m)
    (hs : SigmaCriterion k p m) :
    m.Abundant ↔ 2 ^ (k + 1) < p + 3 := by
  have h := sum_properDivisors_balance hm hs
  unfold Nat.Abundant
  omega

/-! ## The hypotheses are satisfiable

`m = 75 = (2 ^ 4 - 1) * (3 + 2)` has `σ 75 = 124 = (2 ^ 5 - 1) * (3 + 1)`, so it satisfies both
hypotheses; the balance identity reads `124 + 32 = 150 + 6`, and `75` is deficient since
`3 + 3 < 2 ^ 5`. -/

theorem isThabitForm_seventyFive : IsThabitForm 4 3 75 := by
  unfold IsThabitForm; norm_num

theorem sigmaCriterion_seventyFive : SigmaCriterion 4 3 75 := by
  unfold SigmaCriterion; decide

example : σ 1 75 + 2 ^ 5 = 2 * 75 + (3 + 3) :=
  thabit_balance_identity isThabitForm_seventyFive sigmaCriterion_seventyFive

example : Nat.Deficient 75 :=
  (thabit_deficient_iff isThabitForm_seventyFive sigmaCriterion_seventyFive).2 (by norm_num)

end Brockian.BetrothedNumbers.Dynamics

