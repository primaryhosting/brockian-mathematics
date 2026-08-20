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

theorem thabitSigmaCriterion_iff (k p m : ℕ) :
    ThabitSigmaCriterion k p m ↔
      m = (2 ^ k - 1) * (p + 2) ∧ sigma 1 m = m + 2 ^ k * p + 1 := by
  rw [ThabitSigmaCriterion, sigmaOne_eq_sigma]

/-- **Thabit balance identity**, phrased with Mathlib's `σ₁`. -/
