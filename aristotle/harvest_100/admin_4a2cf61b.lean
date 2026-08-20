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
def SigmaCriterion (k p m : ℕ) : Prop :=
  m = (2 ^ k - 1) * (p + 2) ∧ σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)

/--
**Thabit balance identity.**  Under the delivered sigma criterion, the divisor sum of
`m = (2 ^ k - 1) * (p + 2)` satisfies the subtraction-free balance identity

`σ m + 2 ^ (k + 1) = 2 * m + (p + 3)`.
-/
theorem thabit_balance_identity {k p m : ℕ} (h : SigmaCriterion k p m) :
    σ 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  obtain ⟨hm, hs⟩ := h
  -- write `2 ^ k = t + 1` with `t = 2 ^ k - 1`, eliminating natural subtraction
  obtain ⟨t, ht⟩ : ∃ t : ℕ, 2 ^ k = t + 1 :=
    ⟨2 ^ k - 1, (Nat.succ_pred_eq_of_pos (Nat.two_pow_pos k)).symm⟩
  have htm : m = t * (p + 2) := by
    rw [hm, ht]; simp
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * t + 2 := by
    rw [pow_succ, ht]; ring
  rw [hpow] at hs ⊢
  -- cancel the additive term `p + 1` on both sides
  refine Nat.add_right_cancel (m := p + 1) ?_
  calc σ 1 m + (2 * t + 2) + (p + 1)
      = (σ 1 m + (p + 1)) + (2 * t + 2) := by ring
    _ = (2 * t + 2) * (p + 1) + (2 * t + 2) := by rw [hs]
    _ = (2 * t + 2) * (p + 2) := by ring
    _ = 2 * (t * (p + 2)) + (p + 3) + (p + 1) := by ring
    _ = 2 * m + (p + 3) + (p + 1) := by rw [htm]

/-- Under the delivered sigma criterion, `m` is **deficient** iff `p + 3 < 2 ^ (k + 1)`. -/
theorem thabit_deficient_iff {k p m : ℕ} (h : SigmaCriterion k p m) :
    σ 1 m < 2 * m ↔ p + 3 < 2 ^ (k + 1) := by
  have := thabit_balance_identity h
  omega

/-- Under the delivered sigma criterion, `m` is **perfect** iff `p + 3 = 2 ^ (k + 1)`. -/
theorem thabit_perfect_iff {k p m : ℕ} (h : SigmaCriterion k p m) :
    σ 1 m = 2 * m ↔ p + 3 = 2 ^ (k + 1) := by
  have := thabit_balance_identity h
  omega

/-- Under the delivered sigma criterion, `m` is **abundant** iff `2 ^ (k + 1) < p + 3`. -/
theorem thabit_abundant_iff {k p m : ℕ} (h : SigmaCriterion k p m) :
    2 * m < σ 1 m ↔ 2 ^ (k + 1) < p + 3 := by
  have := thabit_balance_identity h
  omega

/-- Explicit (subtraction-carrying) form of the delivered sigma criterion. -/
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
theorem thabit_balance_identity_int {k p m : ℕ} (h : SigmaCriterion k p m) :
    (σ 1 m : ℤ) + 2 ^ (k + 1) = 2 * (m : ℤ) + ((p : ℤ) + 3) := by
  have := thabit_balance_identity h
  exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) this

/-- The criterion is not vacuous: `k = 1`, `p = 0`, `m = 2` satisfies it. -/
theorem sigmaCriterion_two : SigmaCriterion 1 0 2 := by
  constructor
  · norm_num
  · decide

end Brockian.BetrothedNumbers.Dynamics

-- Axiom audit
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_deficient_iff
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_perfect_iff
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_abundant_iff
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_sigma_eq
#print axioms Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity_int
#print axioms Brockian.BetrothedNumbers.Dynamics.sigmaCriterion_two

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

