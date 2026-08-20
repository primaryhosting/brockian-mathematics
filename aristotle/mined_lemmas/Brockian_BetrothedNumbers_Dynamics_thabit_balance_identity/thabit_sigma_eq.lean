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

theorem thabit_sigma_eq {k p m : ℕ} (h : SigmaCriterion k p m) :
    σ 1 m = (2 ^ (k + 1) - 1) * (p + 1) := by
  obtain ⟨-, hs⟩ := h
  obtain ⟨t, ht⟩ : ∃ t : ℕ, 2 ^ (k + 1) = t + 1 :=
    ⟨2 ^ (k + 1) - 1, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos (k + 1))).symm⟩
  rw [ht] at hs ⊢
  simp only [Nat.add_sub_cancel]
  refine Nat.add_right_cancel (m := p + 1) ?_
  rw [hs]
  ring

/-- Integer form of the Thabit balance identity. -/
