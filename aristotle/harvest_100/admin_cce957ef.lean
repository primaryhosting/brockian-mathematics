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

/-- The Thabit-style candidate `m = (2^k - 1) * (p + 2)`. -/
def thabitCandidate (k p : ℕ) : ℕ := (2 ^ k - 1) * (p + 2)

/-- The Thabit-style partner `n = 2^k * p`. -/
def thabitPartner (k p : ℕ) : ℕ := 2 ^ k * p

/-- The delivered (subtraction-free) sigma criterion for the Thabit-style pair:
`σ(m) = (2^(k+1) - 1)(p + 1)`. -/
def SigmaCriterion (k p : ℕ) : Prop :=
  σ 1 (thabitCandidate k p) = (2 ^ (k + 1) - 1) * (p + 1)

/-- The right-hand side of the sigma criterion is exactly the betrothed (quasi-amicable)
value `m + n + 1` for the Thabit-style pair `m = (2^k - 1)(p + 2)`, `n = 2^k p`. -/
theorem sigmaCriterion_rhs_eq (k p : ℕ) :
    (2 ^ (k + 1) - 1) * (p + 1) = thabitCandidate k p + thabitPartner k p + 1 := by
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ k = a + 1 :=
    ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  simp only [thabitCandidate, thabitPartner, pow_succ, ha, Nat.add_sub_cancel]
  have h : (a + 1) * 2 - 1 = 2 * a + 1 := by omega
  rw [h]
  ring

/-- The sigma criterion says precisely that `σ(m) = m + n + 1`, i.e. that `m` satisfies the
betrothed-number condition relative to its Thabit partner `n`. -/
theorem sigmaCriterion_iff (k p : ℕ) :
    SigmaCriterion k p ↔
      σ 1 (thabitCandidate k p) = thabitCandidate k p + thabitPartner k p + 1 := by
  rw [SigmaCriterion, sigmaCriterion_rhs_eq]

/-- **Thabit balance identity.** Under the delivered sigma criterion, the subtraction-free
balance `σ(m) + 2^(k+1) = 2m + (p + 3)` holds for `m = (2^k - 1)(p + 2)`. -/
theorem thabit_balance_identity (k p : ℕ) (h : SigmaCriterion k p) :
    σ 1 (thabitCandidate k p) + 2 ^ (k + 1) = 2 * thabitCandidate k p + (p + 3) := by
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ k = a + 1 :=
    ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  rw [SigmaCriterion] at h
  rw [h]
  simp only [thabitCandidate, pow_succ, ha, Nat.add_sub_cancel]
  have h2 : (a + 1) * 2 - 1 = 2 * a + 1 := by omega
  rw [h2]
  ring

/-- Deficiency comparison: under the sigma criterion, `m` is deficient iff `p + 3 < 2^(k+1)`. -/
theorem thabit_deficient_iff (k p : ℕ) (h : SigmaCriterion k p) :
    σ 1 (thabitCandidate k p) < 2 * thabitCandidate k p ↔ p + 3 < 2 ^ (k + 1) := by
  have := thabit_balance_identity k p h
  omega

/-- Perfection comparison: under the sigma criterion, `m` is perfect iff `p + 3 = 2^(k+1)`. -/
theorem thabit_perfect_iff (k p : ℕ) (h : SigmaCriterion k p) :
    σ 1 (thabitCandidate k p) = 2 * thabitCandidate k p ↔ p + 3 = 2 ^ (k + 1) := by
  have := thabit_balance_identity k p h
  omega

/-- Abundance comparison: under the sigma criterion, `m` is abundant iff `2^(k+1) < p + 3`. -/
theorem thabit_abundant_iff (k p : ℕ) (h : SigmaCriterion k p) :
    2 * thabitCandidate k p < σ 1 (thabitCandidate k p) ↔ 2 ^ (k + 1) < p + 3 := by
  have := thabit_balance_identity k p h
  omega

/-! ### Non-vacuity: concrete instances of the sigma criterion -/

/-- `k = 1, p = 0`: `m = 2`, `n = 0`, `σ(2) = 3 = 2 + 0 + 1`. -/
theorem sigmaCriterion_one_zero : SigmaCriterion 1 0 := by
  unfold SigmaCriterion thabitCandidate; decide

/-- `k = 4, p = 3`: `m = 75`, `n = 48`, `σ(75) = 124 = 75 + 48 + 1`
(the betrothed pair `(48, 75)`). -/
theorem sigmaCriterion_four_three : SigmaCriterion 4 3 := by
  unfold SigmaCriterion thabitCandidate; decide

set_option maxRecDepth 10000 in
/-- `k = 4, p = 103`: `m = 1575`, `n = 1648`, `σ(1575) = 3224 = 1575 + 1648 + 1`. -/
theorem sigmaCriterion_four_onehundredthree : SigmaCriterion 4 103 := by
  unfold SigmaCriterion thabitCandidate; decide

example : σ 1 (thabitCandidate 4 3) < 2 * thabitCandidate 4 3 :=
  (thabit_deficient_iff 4 3 sigmaCriterion_four_three).2 (by norm_num)

end Brockian.BetrothedNumbers.Dynamics

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

