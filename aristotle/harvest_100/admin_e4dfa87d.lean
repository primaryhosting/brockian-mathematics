import Mathlib

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate `m = (2^k - 1)(p + 2)`. -/
def thabitM (k p : ℕ) : ℕ := (2 ^ k - 1) * (p + 2)

/-- The Thabit-style partner `n = 2^k * p`. -/
def thabitPartner (k p : ℕ) : ℕ := 2 ^ k * p

/-- The delivered sigma criterion: `m = (2^k - 1)(p + 2)` and its Thabit partner
`n = 2^k * p` form a betrothed (quasi-amicable) configuration for `m`, i.e.
`σ(m) = m + n + 1`. -/
def SigmaCriterion (k p : ℕ) : Prop :=
  sigma 1 (thabitM k p) = thabitM k p + thabitPartner k p + 1

/-- Subtraction-free description of `thabitM`. -/
lemma thabitM_add (k p : ℕ) : thabitM k p + (p + 2) = 2 ^ k * (p + 2) := by
  unfold thabitM
  rw [Nat.sub_mul, one_mul]
  exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k))

/-- Subtraction-free description of `thabitPartner`. -/
lemma thabitPartner_add (k p : ℕ) :
    thabitPartner k p + 2 ^ k * 2 = 2 ^ k * (p + 2) := by
  unfold thabitPartner; ring

/-- **Thabit balance identity.** Under the delivered sigma criterion, the
subtraction-free balance identity `σ(m) + 2^(k+1) = 2m + (p + 3)` holds for
`m = (2^k - 1)(p + 2)`. -/
theorem thabit_balance_identity (k p : ℕ) (h : SigmaCriterion k p) :
    sigma 1 (thabitM k p) + 2 ^ (k + 1) = 2 * thabitM k p + (p + 3) := by
  have hm := thabitM_add k p
  have hpart := thabitPartner_add k p
  have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by ring
  rw [SigmaCriterion] at h
  rw [h, hpow]
  omega

/-- The balance identity is in fact *equivalent* to the delivered sigma criterion. -/
theorem thabit_balance_identity_iff (k p : ℕ) :
    sigma 1 (thabitM k p) + 2 ^ (k + 1) = 2 * thabitM k p + (p + 3) ↔ SigmaCriterion k p := by
  refine ⟨fun h => ?_, thabit_balance_identity k p⟩
  have hm := thabitM_add k p
  have hpart := thabitPartner_add k p
  have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by ring
  rw [hpow] at h
  rw [SigmaCriterion]
  omega

/-- Deficiency comparison: `m` is deficient iff `p + 3 < 2^(k+1)`. -/
theorem thabit_deficient_iff (k p : ℕ) (h : SigmaCriterion k p) :
    sigma 1 (thabitM k p) < 2 * thabitM k p ↔ p + 3 < 2 ^ (k + 1) := by
  have hb := thabit_balance_identity k p h
  omega

/-- Perfection comparison: `m` is perfect iff `p + 3 = 2^(k+1)`. -/
theorem thabit_perfect_iff (k p : ℕ) (h : SigmaCriterion k p) :
    sigma 1 (thabitM k p) = 2 * thabitM k p ↔ p + 3 = 2 ^ (k + 1) := by
  have hb := thabit_balance_identity k p h
  omega

/-- Abundance comparison: `m` is abundant iff `2^(k+1) < p + 3`. -/
theorem thabit_abundant_iff (k p : ℕ) (h : SigmaCriterion k p) :
    2 * thabitM k p < sigma 1 (thabitM k p) ↔ 2 ^ (k + 1) < p + 3 := by
  have hb := thabit_balance_identity k p h
  omega

/-- The criterion is not vacuous: `k = 4`, `p = 3` realises the betrothed pair
`(48, 75)`, with `m = 75` and partner `n = 48`. -/
theorem sigmaCriterion_four_three : SigmaCriterion 4 3 := by
  rw [SigmaCriterion, sigma_one_apply]
  decide

lemma thabitM_four_three : thabitM 4 3 = 75 := by decide

lemma thabitPartner_four_three : thabitPartner 4 3 = 48 := by decide

/-- In the witness case `p + 3 = 6 < 32 = 2^(k+1)`, so `m = 75` is deficient. -/
example : sigma 1 (thabitM 4 3) < 2 * thabitM 4 3 := by
  rw [thabit_deficient_iff 4 3 sigmaCriterion_four_three]
  norm_num

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

