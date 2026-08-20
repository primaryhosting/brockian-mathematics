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

open scoped BigOperators
open scoped Nat
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.BetrothedNumbers.Dynamics

/--
The *delivered sigma criterion* for a Thabit-type parameter pair `(k, p)` and a candidate
number `m`:

* `m` is the Thabit-type value `(2 ^ k - 1) * (p + 2)`, and
* the divisor sum of `m` satisfies the subtraction-free relation
  `σ m + (p + 1) = 2 ^ (k + 1) * (p + 1)`
  (i.e. `σ m = (2 ^ (k + 1) - 1) * (p + 1)`, stated without natural subtraction).
-/

theorem thabit_balance_identity_int {k p m : ℕ} (h : SigmaCriterion k p m) :
    (σ 1 m : ℤ) + 2 ^ (k + 1) = 2 * (m : ℤ) + ((p : ℤ) + 3) := by
  have := thabit_balance_identity h
  exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) this

/-- The criterion is not vacuous: `k = 1`, `p = 0`, `m = 2` satisfies it. -/
