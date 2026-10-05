import Mathlib
import RequestProject.ThabitBalance

/-!
# Bridge to Mathlib's `σ₁`

The target file `ThabitBalance.lean` is import-free (its header comment must be the very first
thing in the file, which precludes an `import` command), so it uses its own elementary
sum-of-divisors function `sigmaOne`.  Here we prove that `sigmaOne` agrees with Mathlib's
`ArithmeticFunction.sigma 1`, and restate the balance identity together with the
deficient/perfect/abundant comparisons in Mathlib's language.
-/

open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

theorem sigmaAux_eq_sum (m : Nat) :
    ∀ n : Nat, sigmaAux m n = ∑ d ∈ Finset.range (n + 1), if d ∣ m then d else 0
  | 0 => by simp [sigmaAux]
  | n + 1 => by
      rw [Finset.sum_range_succ, ← sigmaAux_eq_sum m n]
      rfl

theorem divisors_eq_filter_range {m : Nat} (hm : m ≠ 0) :
    m.divisors = (Finset.range (m + 1)).filter (· ∣ m) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hd, -⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hd), hd⟩
  · rintro ⟨-, hd⟩
    exact ⟨hd, hm⟩

/-- The elementary `sigmaOne` of the target file agrees with Mathlib's `σ₁`. -/
theorem sigmaOne_eq_sigma_one (m : Nat) : sigmaOne m = σ 1 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sigmaOne, sigmaAux]
  · rw [sigmaOne, sigmaAux_eq_sum, ArithmeticFunction.sigma_one_apply,
      divisors_eq_filter_range (Nat.ne_of_gt hm).symm, Finset.sum_filter]

/-- **Thabit balance identity**, stated with Mathlib's `σ₁`. -/
theorem thabit_balance_identity_sigma {k p m : Nat}
    (hshape : m + (p + 2) = 2 ^ k * (p + 2))
    (hsigma : σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)) :
    σ 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  rw [← sigmaOne_eq_sigma_one] at hsigma ⊢
  exact thabit_balance_identity hshape hsigma

/-- Deficiency comparison in Mathlib's language. -/
theorem thabit_deficient_iff_sigma {k p m : Nat}
    (hshape : m + (p + 2) = 2 ^ k * (p + 2))
    (hsigma : σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)) :
    σ 1 m < 2 * m ↔ p + 3 < 2 ^ (k + 1) := by
  have h := thabit_balance_identity_sigma hshape hsigma
  omega

/-- Perfection comparison in Mathlib's language. -/
theorem thabit_perfect_iff_sigma {k p m : Nat}
    (hshape : m + (p + 2) = 2 ^ k * (p + 2))
    (hsigma : σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)) :
    σ 1 m = 2 * m ↔ p + 3 = 2 ^ (k + 1) := by
  have h := thabit_balance_identity_sigma hshape hsigma
  omega

/-- Abundance comparison in Mathlib's language. -/
theorem thabit_abundant_iff_sigma {k p m : Nat}
    (hshape : m + (p + 2) = 2 ^ k * (p + 2))
    (hsigma : σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)) :
    2 * m < σ 1 m ↔ 2 ^ (k + 1) < p + 3 := by
  have h := thabit_balance_identity_sigma hshape hsigma
  omega

end Brockian.BetrothedNumbers.Dynamics

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers.Dynamics

/-- Auxiliary accumulator: `sigmaAux m n` is the sum of the divisors of `m` that are `≤ n`
(only positive divisors contribute). -/
def sigmaAux (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sigmaAux m n + (if n + 1 ∣ m then n + 1 else 0)

/-- The sum-of-divisors function `σ₁`.  It agrees with Mathlib's `Nat.sigma 1`; see
`Brockian.BetrothedNumbers.Dynamics.sigmaOne_eq_sigma_one` in `ThabitBalanceMathlib.lean`. -/
def sigmaOne (m : Nat) : Nat := sigmaAux m m

/-- The Thabit-style shape criterion, written subtraction-free:
`m + (p + 2) = 2 ^ k * (p + 2)`, i.e. `m = (2 ^ k - 1) * (p + 2)`. -/
def ThabitShape (k p m : Nat) : Prop := m + (p + 2) = 2 ^ k * (p + 2)

/-- The delivered sigma criterion, written subtraction-free:
`σ₁ m + (p + 1) = 2 ^ (k + 1) * (p + 1)`, i.e. `σ₁ m = (2 ^ (k + 1) - 1) * (p + 1)`. -/
def SigmaCriterion (k p m : Nat) : Prop :=
  sigmaOne m + (p + 1) = 2 ^ (k + 1) * (p + 1)

/-- **Thabit balance identity.**  If `m = (2 ^ k - 1) * (p + 2)` (in subtraction-free form) and
`m` satisfies the delivered sigma criterion `σ₁ m = (2 ^ (k + 1) - 1) * (p + 1)`, then the
subtraction-free balance identity `σ₁ m + 2 ^ (k + 1) = 2 * m + (p + 3)` holds. -/
theorem thabit_balance_identity {k p m : Nat}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    sigmaOne m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  unfold ThabitShape at hshape
  unfold SigmaCriterion at hsigma
  have hp : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [hp] at hsigma ⊢
  have h1 : 2 ^ k * (p + 2) = 2 ^ k * p + 2 * 2 ^ k := by
    rw [Nat.mul_add, Nat.mul_comm (2 ^ k) 2]
  have h2 : 2 * 2 ^ k * (p + 1) = 2 * (2 ^ k * p) + 2 * 2 ^ k := by
    rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_one]
  rw [h1] at hshape
  rw [h2] at hsigma
  omega

/-- The two criteria are simultaneously satisfiable, so the balance identity is not vacuous:
take `k = 1`, `p = 0`, `m = 2` (then `σ₁ 2 = 3` and `3 + 4 = 2 * 2 + 3`). -/
theorem thabit_hypotheses_satisfiable : ThabitShape 1 0 2 ∧ SigmaCriterion 1 0 2 := by
  constructor
  · show 2 + (0 + 2) = 2 ^ 1 * (0 + 2)
    decide
  · show sigmaOne 2 + (0 + 1) = 2 ^ (1 + 1) * (0 + 1)
    decide

/-- Deficiency comparison: `m` is deficient iff `p + 3 < 2 ^ (k + 1)`. -/
theorem thabit_deficient_iff {k p m : Nat}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    sigmaOne m < 2 * m ↔ p + 3 < 2 ^ (k + 1) := by
  have h := thabit_balance_identity hshape hsigma
  omega

/-- Perfection comparison: `m` is perfect iff `p + 3 = 2 ^ (k + 1)`. -/
theorem thabit_perfect_iff {k p m : Nat}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    sigmaOne m = 2 * m ↔ p + 3 = 2 ^ (k + 1) := by
  have h := thabit_balance_identity hshape hsigma
  omega

/-- Abundance comparison: `m` is abundant iff `2 ^ (k + 1) < p + 3`. -/
theorem thabit_abundant_iff {k p m : Nat}
    (hshape : ThabitShape k p m) (hsigma : SigmaCriterion k p m) :
    2 * m < sigmaOne m ↔ 2 ^ (k + 1) < p + 3 := by
  have h := thabit_balance_identity hshape hsigma
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

