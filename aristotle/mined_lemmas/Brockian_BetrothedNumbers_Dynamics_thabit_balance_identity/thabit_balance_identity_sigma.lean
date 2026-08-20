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

theorem thabit_balance_identity_sigma {k p m : ℕ} (hm : m = (2 ^ k - 1) * (p + 2))
    (hs : sigma 1 m = m + 2 ^ k * p + 1) :
    sigma 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  have h : ThabitSigmaCriterion k p m := (thabitSigmaCriterion_iff k p m).2 ⟨hm, hs⟩
  have := thabit_balance_identity h
  rwa [sigmaOne_eq_sigma] at this

/-- Deficiency comparison, phrased with Mathlib's `σ₁`. -/
