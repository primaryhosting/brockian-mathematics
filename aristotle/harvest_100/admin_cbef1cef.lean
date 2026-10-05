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

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate attached to the parameters `k` and `p`:
`m = (2 ^ k - 1) * (p + 2)`.  (The subtraction is harmless: `1 ≤ 2 ^ k`.) -/
def thabitCandidate (k p : ℕ) : ℕ := (2 ^ k - 1) * (p + 2)

/-- The delivered sigma criterion for the Thabit-style candidate, written in
subtraction-free form:  `σ₁(m) + (p + 1) = 2 ^ (k + 1) * (p + 1)`, i.e.
`σ₁(m) = (2 ^ (k + 1) - 1) * (p + 1)`. -/
def SigmaCriterion (k p : ℕ) : Prop :=
  σ 1 (thabitCandidate k p) + (p + 1) = 2 ^ (k + 1) * (p + 1)

/-- The criterion is not vacuous: `k = 4`, `p = 3` gives `m = 75`, and
`σ₁(75) = 124 = 31 * 4`. -/
theorem sigmaCriterion_four_three : SigmaCriterion 4 3 := by
  simp only [SigmaCriterion, thabitCandidate, ArithmeticFunction.sigma_one_apply]
  decide

/-- Another witness: `k = 1`, `p = 0` gives `m = 2` and `σ₁(2) = 3 = 3 * 1`. -/
theorem sigmaCriterion_one_zero : SigmaCriterion 1 0 := by
  simp only [SigmaCriterion, thabitCandidate, ArithmeticFunction.sigma_one_apply]
  decide

/-- **Thabit balance identity.**  Under the delivered sigma criterion, the
Thabit-style candidate `m = (2 ^ k - 1) * (p + 2)` satisfies the
subtraction-free balance identity `σ₁(m) + 2 ^ (k + 1) = 2 * m + (p + 3)`. -/
theorem thabit_balance_identity {k p : ℕ} (h : SigmaCriterion k p) :
    σ 1 (thabitCandidate k p) + 2 ^ (k + 1) = 2 * thabitCandidate k p + (p + 3) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, 2 ^ k = t + 1 :=
    ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * (t + 1) := by rw [pow_succ, ht]; ring
  have hm : thabitCandidate k p = t * (p + 2) := by
    simp [thabitCandidate, ht]
  rw [SigmaCriterion, hm, hpow] at h
  rw [hm, hpow]
  set S := σ 1 (t * (p + 2)) with hS
  obtain ⟨u, hu⟩ : ∃ u : ℕ, t * p = u := ⟨_, rfl⟩
  have h' : S + (p + 1) = 2 * u + 2 * t + 2 * p + 2 := by
    rw [h, ← hu]; ring
  have hg : 2 * (t * (p + 2)) + (p + 3) = 2 * u + 4 * t + p + 3 := by
    rw [← hu]; ring
  rw [hg]
  omega

/-- Under the sigma criterion the candidate is positive. -/
theorem thabitCandidate_pos {k p : ℕ} (h : SigmaCriterion k p) :
    0 < thabitCandidate k p := by
  rcases Nat.eq_zero_or_pos (thabitCandidate k p) with hm | hm
  · rw [SigmaCriterion, hm] at h
    have h0 : σ 1 0 = 0 := by simp
    rw [h0, zero_add] at h
    have h2 : 2 ≤ 2 ^ (k + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  · exact hm

/-- The balance identity, transported to the sum of proper divisors. -/
theorem thabit_properDivisors_balance {k p : ℕ} (h : SigmaCriterion k p) :
    (∑ i ∈ Nat.properDivisors (thabitCandidate k p), i) + 2 ^ (k + 1)
      = thabitCandidate k p + (p + 3) := by
  have hb := thabit_balance_identity h
  rw [ArithmeticFunction.sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self] at hb
  omega

/-- **Deficiency comparison.** -/
theorem thabit_deficient_iff {k p : ℕ} (h : SigmaCriterion k p) :
    (thabitCandidate k p).Deficient ↔ p + 3 < 2 ^ (k + 1) := by
  have hb := thabit_properDivisors_balance h
  unfold Nat.Deficient
  omega

/-- **Perfection comparison.** -/
theorem thabit_perfect_iff {k p : ℕ} (h : SigmaCriterion k p) :
    (thabitCandidate k p).Perfect ↔ p + 3 = 2 ^ (k + 1) := by
  have hb := thabit_properDivisors_balance h
  rw [Nat.perfect_iff_sum_properDivisors (thabitCandidate_pos h)]
  omega

/-- **Abundance comparison.** -/
theorem thabit_abundant_iff {k p : ℕ} (h : SigmaCriterion k p) :
    (thabitCandidate k p).Abundant ↔ 2 ^ (k + 1) < p + 3 := by
  have hb := thabit_properDivisors_balance h
  unfold Nat.Abundant
  omega

end Brockian.BetrothedNumbers.Dynamics

