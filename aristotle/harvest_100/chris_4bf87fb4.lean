import Mathlib
import RequestProject.ThabitBalanceIdentity

/-!
# Thabit Balance Identity — Mathlib interface

This file connects the self-contained divisor-sum `sigmaOne` used in
`RequestProject.ThabitBalanceIdentity` with Mathlib's `ArithmeticFunction.sigma 1`, and restates
the Thabit balance identity and the deficient/perfect/abundant comparisons in Mathlib terms.
-/

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- `sigmaOne` is Mathlib's sum-of-divisors function `σ₁`. -/
theorem sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply]
  have h1 : n.divisors = (Finset.range (n + 1)).filter (fun d => d != 0 && n % d == 0) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range, Bool.and_eq_true,
      bne_iff_ne, ne_eq, beq_iff_eq]
    constructor
    · rintro ⟨hd, hn⟩
      have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
      have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd)
      exact ⟨by omega, hd0, Nat.mod_eq_zero_of_dvd hd⟩
    · rintro ⟨_, h0, hd⟩
      exact ⟨Nat.dvd_of_mod_eq_zero hd, by rintro rfl; simp at hd ⊢; omega⟩
  rw [h1, Finset.sum_eq_multiset_sum]
  simp only [sigmaOne, Finset.filter, Finset.range, Multiset.range, Multiset.filter_coe,
    Multiset.map_id', Multiset.sum_coe]
  simp
  rfl

/-- The Thabit sigma criterion, phrased with Mathlib's `σ₁`. -/
theorem thabitSigmaCriterion_iff (k p m : ℕ) :
    ThabitSigmaCriterion k p m ↔
      m = (2 ^ k - 1) * (p + 2) ∧ sigma 1 m = m + 2 ^ k * p + 1 := by
  rw [ThabitSigmaCriterion, sigmaOne_eq_sigma]

/-- **Thabit balance identity**, phrased with Mathlib's `σ₁`. -/
theorem thabit_balance_identity_sigma {k p m : ℕ} (hm : m = (2 ^ k - 1) * (p + 2))
    (hs : sigma 1 m = m + 2 ^ k * p + 1) :
    sigma 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  have h : ThabitSigmaCriterion k p m := (thabitSigmaCriterion_iff k p m).2 ⟨hm, hs⟩
  have := thabit_balance_identity h
  rwa [sigmaOne_eq_sigma] at this

/-- Deficiency comparison, phrased with Mathlib's `σ₁`. -/
theorem thabit_deficient_iff_sigma {k p m : ℕ} (hm : m = (2 ^ k - 1) * (p + 2))
    (hs : sigma 1 m = m + 2 ^ k * p + 1) :
    sigma 1 m < 2 * m ↔ p + 3 < 2 ^ (k + 1) := by
  have hid := thabit_balance_identity_sigma hm hs
  omega

/-- Perfection comparison, phrased with Mathlib's `σ₁`. -/
theorem thabit_perfect_iff_sigma {k p m : ℕ} (hm : m = (2 ^ k - 1) * (p + 2))
    (hs : sigma 1 m = m + 2 ^ k * p + 1) :
    sigma 1 m = 2 * m ↔ p + 3 = 2 ^ (k + 1) := by
  have hid := thabit_balance_identity_sigma hm hs
  omega

/-- Abundance comparison, phrased with Mathlib's `σ₁`. -/
theorem thabit_abundant_iff_sigma {k p m : ℕ} (hm : m = (2 ^ k - 1) * (p + 2))
    (hs : sigma 1 m = m + 2 ^ k * p + 1) :
    2 * m < sigma 1 m ↔ 2 ^ (k + 1) < p + 3 := by
  have hid := thabit_balance_identity_sigma hm hs
  omega

/-- The betrothed pair `(48, 75)`: `σ(75) = 75 + 48 + 1`, of Thabit type with `k = 4`, `p = 3`. -/
theorem sigma_seventyFive : sigma 1 75 = 75 + 2 ^ 4 * 3 + 1 := by
  rw [← sigmaOne_eq_sigma]
  rfl

end Brockian.BetrothedNumbers.Dynamics

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers.Dynamics

/-- `sigmaOne n` is the sum of the (positive) divisors of `n`, i.e. the classical `σ(n)`.
(It is shown to agree with Mathlib's `ArithmeticFunction.sigma 1` in
`RequestProject.ThabitBalanceIdentityMathlib`.) -/
def sigmaOne (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun d => d != 0 && n % d == 0)).sum

/-- The **Thabit sigma criterion** for a Thabit-type betrothed (quasi-amicable) configuration:
`m` has the Thabit shape `(2 ^ k - 1) * (p + 2)` and satisfies the betrothed relation
`σ(m) = m + n + 1` with partner `n = 2 ^ k * p`. -/
def ThabitSigmaCriterion (k p m : Nat) : Prop :=
  m = (2 ^ k - 1) * (p + 2) ∧ sigmaOne m = m + 2 ^ k * p + 1

/-- The classical betrothed pair `(48, 75)` is of Thabit type, with `k = 4`, `p = 3`,
`m = (2 ^ 4 - 1) * 5 = 75` and partner `2 ^ 4 * 3 = 48`.  Hence the criterion is not vacuous. -/
theorem thabitSigmaCriterion_seventyFive : ThabitSigmaCriterion 4 3 75 :=
  ⟨rfl, rfl⟩

/-- Subtraction-free form of the Thabit shape. -/
theorem thabit_shape_add {k p m : Nat} (hm : m = (2 ^ k - 1) * (p + 2)) :
    m + (p + 2) = 2 ^ k * p + 2 * 2 ^ k := by
  have hA : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ k = a + 1 := ⟨2 ^ k - 1, by omega⟩
  rw [hm, ha]
  simp [Nat.succ_mul, Nat.mul_add]
  omega

/-- **Thabit balance identity.** Under the Thabit sigma criterion, the subtraction-free
balance identity `σ(m) + 2 ^ (k + 1) = 2 * m + (p + 3)` holds. -/
theorem thabit_balance_identity {k p m : Nat} (h : ThabitSigmaCriterion k p m) :
    sigmaOne m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  obtain ⟨hm, hs⟩ := h
  have h1 : m + (p + 2) = 2 ^ k * p + 2 * 2 ^ k := thabit_shape_add hm
  have h2 : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [hs, h2]
  omega

/-- Deficiency comparison: `m` is deficient iff `p + 3 < 2 ^ (k + 1)`. -/
theorem thabit_deficient_iff {k p m : Nat} (h : ThabitSigmaCriterion k p m) :
    sigmaOne m < 2 * m ↔ p + 3 < 2 ^ (k + 1) := by
  have hid := thabit_balance_identity h
  omega

/-- Perfection comparison: `m` is perfect iff `p + 3 = 2 ^ (k + 1)`. -/
theorem thabit_perfect_iff {k p m : Nat} (h : ThabitSigmaCriterion k p m) :
    sigmaOne m = 2 * m ↔ p + 3 = 2 ^ (k + 1) := by
  have hid := thabit_balance_identity h
  omega

/-- Abundance comparison: `m` is abundant iff `2 ^ (k + 1) < p + 3`. -/
theorem thabit_abundant_iff {k p m : Nat} (h : ThabitSigmaCriterion k p m) :
    2 * m < sigmaOne m ↔ 2 ^ (k + 1) < p + 3 := by
  have hid := thabit_balance_identity h
  omega

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

