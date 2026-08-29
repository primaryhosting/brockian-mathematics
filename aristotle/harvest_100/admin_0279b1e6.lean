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

## Contents

For a Thabit-type candidate `m = (2 ^ k - 1) * (p + 2)` satisfying the delivered
sigma criterion `σ₁ m = (2 ^ (k + 1) - 1) * (p + 1)`, we prove the subtraction-free
balance identity

  `σ₁ m + 2 ^ (k + 1) = 2 * m + (p + 3)`

and deduce the deficient / perfect / abundant comparison `iff` theorems:
`m` is deficient (resp. perfect, abundant) exactly when `p + 3 < 2 ^ (k + 1)`
(resp. `=`, `>`).

The criterion is non-vacuous: `(k, p) = (4, 3)` gives `m = 75`, one half of the
betrothed (quasi-amicable) pair `(48, 75)`.
-/

set_option autoImplicit false

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The Thabit-type candidate `m = (2 ^ k - 1) * (p + 2)`. -/
def thabitCandidate (k p : ℕ) : ℕ := (2 ^ k - 1) * (p + 2)

/-- The delivered sigma criterion for the Thabit-type candidate:
`σ₁ ((2 ^ k - 1) * (p + 2)) = (2 ^ (k + 1) - 1) * (p + 1)`. -/
def SigmaCriterion (k p : ℕ) : Prop :=
  sigma 1 (thabitCandidate k p) = (2 ^ (k + 1) - 1) * (p + 1)

/-- The subtraction-free balance identity: under the delivered sigma criterion, the
Thabit-type candidate `m = (2 ^ k - 1) * (p + 2)` satisfies
`σ(m) + 2 ^ (k + 1) = 2 * m + (p + 3)`. -/
theorem thabit_balance_identity (k p : ℕ) (h : SigmaCriterion k p) :
    sigma 1 (thabitCandidate k p) + 2 ^ (k + 1)
      = 2 * thabitCandidate k p + (p + 3) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, 2 ^ k = s + 1 :=
    ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  rw [SigmaCriterion] at h
  rw [h, thabitCandidate, pow_succ, hs]
  have h1 : (s + 1) * 2 - 1 = 2 * s + 1 := by omega
  have h2 : s + 1 - 1 = s := by omega
  rw [h1, h2]
  ring

/-- Deficiency comparison: under the sigma criterion, `m = (2 ^ k - 1) * (p + 2)` is
deficient exactly when `p + 3 < 2 ^ (k + 1)`. -/
theorem thabit_deficient_iff (k p : ℕ) (h : SigmaCriterion k p) :
    sigma 1 (thabitCandidate k p) < 2 * thabitCandidate k p ↔ p + 3 < 2 ^ (k + 1) := by
  have := thabit_balance_identity k p h
  omega

/-- Perfection comparison: under the sigma criterion, `m = (2 ^ k - 1) * (p + 2)` is
perfect (in the `σ(m) = 2m` sense) exactly when `p + 3 = 2 ^ (k + 1)`. -/
theorem thabit_perfect_iff (k p : ℕ) (h : SigmaCriterion k p) :
    sigma 1 (thabitCandidate k p) = 2 * thabitCandidate k p ↔ p + 3 = 2 ^ (k + 1) := by
  have := thabit_balance_identity k p h
  omega

/-- Abundance comparison: under the sigma criterion, `m = (2 ^ k - 1) * (p + 2)` is
abundant exactly when `2 ^ (k + 1) < p + 3`. -/
theorem thabit_abundant_iff (k p : ℕ) (h : SigmaCriterion k p) :
    2 * thabitCandidate k p < sigma 1 (thabitCandidate k p) ↔ 2 ^ (k + 1) < p + 3 := by
  have := thabit_balance_identity k p h
  omega

/-- Perfection in Mathlib's sense (`Nat.Perfect`), for a positive candidate. -/
theorem thabit_nat_perfect_iff (k p : ℕ) (h : SigmaCriterion k p)
    (hpos : 0 < thabitCandidate k p) :
    Nat.Perfect (thabitCandidate k p) ↔ p + 3 = 2 ^ (k + 1) := by
  rw [Nat.perfect_iff_sigma_eq_two_mul hpos, ← sigma_one_eq_sigmaOne]
  exact thabit_perfect_iff k p h

/-- The sigma criterion is non-vacuous: it holds for `(k, p) = (4, 3)`, i.e. for
`m = 15 * 5 = 75`. -/
theorem sigmaCriterion_four_three : SigmaCriterion 4 3 := by
  rw [SigmaCriterion, thabitCandidate]
  decide

/-- The witness `m = 75` is one half of the betrothed (quasi-amicable) pair `(48, 75)`:
`σ(48) = σ(75) = 48 + 75 + 1`. -/
theorem betrothed_48_75 :
    sigma 1 48 = 48 + 75 + 1 ∧ sigma 1 75 = 48 + 75 + 1 := by
  constructor <;> decide

/-- Instance of the balance identity at the witness `(k, p) = (4, 3)`. -/
example : sigma 1 (thabitCandidate 4 3) + 2 ^ 5 = 2 * thabitCandidate 4 3 + (3 + 3) :=
  thabit_balance_identity 4 3 sigmaCriterion_four_three

/-- The witness `m = 75` is deficient, since `3 + 3 < 2 ^ 5`. -/
example : sigma 1 (thabitCandidate 4 3) < 2 * thabitCandidate 4 3 :=
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

