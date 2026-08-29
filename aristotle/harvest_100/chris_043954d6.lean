/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BetrothedNumbers.Dynamics

open Finset

/-- The sum-of-divisors function `σ₁`. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

@[simp] theorem sigma_eq_sigma_one (n : ℕ) :
    sigma n = ArithmeticFunction.sigma 1 n := by
  simp [sigma, ArithmeticFunction.sigma_apply]

/-- **Thabit shape.** `m` is the Thabit-type number `(2 ^ k - 1) * (p + 2)`, written in the
subtraction-free form `m + (p + 2) = 2 ^ k * (p + 2)`. -/
def ThabitShape (k p m : ℕ) : Prop := m + (p + 2) = 2 ^ k * (p + 2)

/-- **The delivered sigma criterion.** The divisor sum of `m` equals `(2 ^ (k+1) - 1) * (p + 1)`,
written in the subtraction-free form `σ m + (p + 1) = 2 ^ (k+1) * (p + 1)`. -/
def SigmaCriterion (k p m : ℕ) : Prop := sigma m + (p + 1) = 2 ^ (k + 1) * (p + 1)

/-- **Thabit balance identity.**  For a Thabit-type number `m = (2 ^ k - 1) * (p + 2)` satisfying
the delivered sigma criterion `σ m = (2 ^ (k+1) - 1) * (p + 1)`, the subtraction-free balance
identity `σ m + 2 ^ (k+1) = 2 * m + (p + 3)` holds. -/
theorem thabit_balance_identity {k p m : ℕ}
    (hm : ThabitShape k p m) (hs : SigmaCriterion k p m) :
    sigma m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  unfold ThabitShape at hm
  unfold SigmaCriterion at hs
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  -- eliminate `σ m` and `m` against the two subtraction-free hypotheses
  have key : (sigma m + 2 ^ (k + 1)) + ((p + 1) + 2 * (p + 2))
      = (2 * m + (p + 3)) + ((p + 1) + 2 * (p + 2)) := by
    calc (sigma m + 2 ^ (k + 1)) + ((p + 1) + 2 * (p + 2))
        = (sigma m + (p + 1)) + 2 ^ (k + 1) + 2 * (p + 2) := by ring
      _ = 2 ^ (k + 1) * (p + 1) + 2 ^ (k + 1) + 2 * (p + 2) := by rw [hs]
      _ = 2 * (2 ^ k * (p + 2)) + (p + 1) + 2 * (p + 2) - 2 * (p + 2)
            + 0 := by rw [h2]; ring_nf; omega
      _ = 2 * (m + (p + 2)) + (p + 1) + 2 * (p + 2) - 2 * (p + 2) := by rw [hm]
      _ = (2 * m + (p + 3)) + ((p + 1) + 2 * (p + 2)) := by omega
  omega

/-- The hypotheses of `thabit_balance_identity` are satisfiable: `k = 1`, `p = 0`, `m = 2`. -/
example : ThabitShape 1 0 2 ∧ SigmaCriterion 1 0 2 := by
  constructor <;> · unfold ThabitShape SigmaCriterion sigma; decide

/-- **Deficient comparison.** Under the Thabit shape and the sigma criterion, `m` is deficient
(`σ m < 2 * m`) iff `p + 3 < 2 ^ (k+1)`. -/
theorem thabit_deficient_iff {k p m : ℕ}
    (hm : ThabitShape k p m) (hs : SigmaCriterion k p m) :
    sigma m < 2 * m ↔ p + 3 < 2 ^ (k + 1) := by
  have h := thabit_balance_identity hm hs
  omega

/-- **Perfect comparison.** Under the Thabit shape and the sigma criterion, `m` is perfect
(`σ m = 2 * m`) iff `p + 3 = 2 ^ (k+1)`. -/
theorem thabit_perfect_iff {k p m : ℕ}
    (hm : ThabitShape k p m) (hs : SigmaCriterion k p m) :
    sigma m = 2 * m ↔ p + 3 = 2 ^ (k + 1) := by
  have h := thabit_balance_identity hm hs
  omega

/-- **Abundant comparison.** Under the Thabit shape and the sigma criterion, `m` is abundant
(`2 * m < σ m`) iff `2 ^ (k+1) < p + 3`. -/
theorem thabit_abundant_iff {k p m : ℕ}
    (hm : ThabitShape k p m) (hs : SigmaCriterion k p m) :
    2 * m < sigma m ↔ 2 ^ (k + 1) < p + 3 := by
  have h := thabit_balance_identity hm hs
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

