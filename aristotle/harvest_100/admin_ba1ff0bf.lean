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

namespace Brockian.BetrothedNumbers.Dynamics

/-- The delivered **Thabit sigma criterion** for a Thabit-shaped candidate
`m = (2 ^ k - 1) * (p + 2)` with `1 ≤ k`:  the divisor sum of `m` is
`2 * m + (p + 3) - 2 ^ (k + 1)`.  The defining equation is stated over `ℤ`, so
that the truncated subtraction of `ℕ` plays no role. -/
def ThabitSigmaCriterion (k p m : ℕ) : Prop :=
  m = (2 ^ k - 1) * (p + 2) ∧ 1 ≤ k ∧
    ((ArithmeticFunction.sigma 1 m : ℤ) = 2 * (m : ℤ) + (p + 3) - 2 ^ (k + 1))

/-- A Thabit-shaped candidate satisfying the sigma criterion is positive. -/
lemma ThabitSigmaCriterion.pos {k p m : ℕ} (h : ThabitSigmaCriterion k p m) : 0 < m := by
  obtain ⟨hm, hk, -⟩ := h
  subst hm
  have h2 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  exact Nat.mul_pos (by omega) (by omega)

/-- The proper-divisor sum of a candidate satisfying the sigma criterion, over `ℤ`. -/
lemma ThabitSigmaCriterion.properDivisors_sum {k p m : ℕ} (h : ThabitSigmaCriterion k p m) :
    ((∑ i ∈ Nat.properDivisors m, i : ℕ) : ℤ) = (m : ℤ) + (p + 3) - 2 ^ (k + 1) := by
  have hsum : (ArithmeticFunction.sigma 1 m : ℕ)
      = (∑ i ∈ Nat.properDivisors m, i) + m := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have h3 := h.2.2
  rw [hsum] at h3
  push_cast at h3 ⊢
  linarith

/-- **Thabit balance identity.**  For a Thabit-shaped `m = (2 ^ k - 1) * (p + 2)` (with `1 ≤ k`)
satisfying the delivered sigma criterion, the balance identity
`σ(m) + 2 ^ (k + 1) = 2 * m + (p + 3)` holds in `ℕ` — subtraction-free — and the
deficient / perfect / abundant trichotomy for `m` is decided by comparing `p + 3` with
`2 ^ (k + 1)`. -/
theorem thabit_balance_identity {k p m : ℕ} (h : ThabitSigmaCriterion k p m) :
    ArithmeticFunction.sigma 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) ∧
      (Nat.Deficient m ↔ p + 3 < 2 ^ (k + 1)) ∧
      (Nat.Perfect m ↔ p + 3 = 2 ^ (k + 1)) ∧
      (Nat.Abundant m ↔ 2 ^ (k + 1) < p + 3) := by
  have hpos : 0 < m := h.pos
  have hprop := h.properDivisors_sum
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ((ArithmeticFunction.sigma 1 m + 2 ^ (k + 1) : ℕ) : ℤ)
        = ((2 * m + (p + 3) : ℕ) : ℤ) := by
      have h3 := h.2.2
      push_cast at h3 ⊢
      linarith
    exact_mod_cast this
  · rw [Nat.Deficient]
    constructor
    · intro hlt
      have : ((∑ i ∈ Nat.properDivisors m, i : ℕ) : ℤ) < (m : ℤ) := by exact_mod_cast hlt
      have h2 : ((p : ℤ) + 3) < 2 ^ (k + 1) := by linarith [hprop]
      have : ((p + 3 : ℕ) : ℤ) < ((2 ^ (k + 1) : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · intro hlt
      have h2 : ((p + 3 : ℕ) : ℤ) < ((2 ^ (k + 1) : ℕ) : ℤ) := by exact_mod_cast hlt
      push_cast at h2
      have : ((∑ i ∈ Nat.properDivisors m, i : ℕ) : ℤ) < (m : ℤ) := by linarith [hprop]
      exact_mod_cast this
  · rw [Nat.Perfect]
    constructor
    · rintro ⟨heq, -⟩
      have : ((∑ i ∈ Nat.properDivisors m, i : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast heq
      have h2 : ((p + 3 : ℕ) : ℤ) = ((2 ^ (k + 1) : ℕ) : ℤ) := by push_cast; linarith [hprop]
      exact_mod_cast h2
    · intro heq
      have h2 : ((p + 3 : ℕ) : ℤ) = ((2 ^ (k + 1) : ℕ) : ℤ) := by exact_mod_cast heq
      push_cast at h2
      refine ⟨?_, hpos⟩
      have : ((∑ i ∈ Nat.properDivisors m, i : ℕ) : ℤ) = (m : ℤ) := by linarith [hprop]
      exact_mod_cast this
  · rw [Nat.Abundant]
    constructor
    · intro hlt
      have : (m : ℤ) < ((∑ i ∈ Nat.properDivisors m, i : ℕ) : ℤ) := by exact_mod_cast hlt
      have h2 : ((2 ^ (k + 1) : ℕ) : ℤ) < ((p + 3 : ℕ) : ℤ) := by push_cast; linarith [hprop]
      exact_mod_cast h2
    · intro hlt
      have h2 : ((2 ^ (k + 1) : ℕ) : ℤ) < ((p + 3 : ℕ) : ℤ) := by exact_mod_cast hlt
      push_cast at h2
      have : (m : ℤ) < ((∑ i ∈ Nat.properDivisors m, i : ℕ) : ℤ) := by linarith [hprop]
      exact_mod_cast this

/-- The criterion is not vacuous: `k = 4`, `p = 3`, `m = (2 ^ 4 - 1) * 5 = 75` satisfies it. -/
theorem thabitSigmaCriterion_75 : ThabitSigmaCriterion 4 3 75 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have : (ArithmeticFunction.sigma 1 75 : ℕ) = 124 := by
    rw [ArithmeticFunction.sigma_one_apply]; decide
  rw [this]
  norm_num

/-- Consequence of the balance identity in the witness case: `75` is deficient,
since `p + 3 = 6 < 32 = 2 ^ 5`. -/
theorem deficient_75 : Nat.Deficient 75 :=
  (thabit_balance_identity thabitSigmaCriterion_75).2.1.mpr (by norm_num)

end Brockian.BetrothedNumbers.Dynamics

