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

theorem sum_properDivisors_balance {k p m : ℕ} (hm : IsThabitForm k p m)
    (hs : SigmaCriterion k p m) :
    (∑ i ∈ m.properDivisors, i) + m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  have h := thabit_balance_identity hm hs
  rwa [ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self] at h

/-- A Thabit-form number satisfying the sigma criterion is **deficient** exactly when
`p + 3 < 2 ^ (k + 1)`. -/
