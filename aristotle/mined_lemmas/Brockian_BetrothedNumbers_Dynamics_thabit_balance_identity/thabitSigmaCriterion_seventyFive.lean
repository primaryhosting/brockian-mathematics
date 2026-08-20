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

theorem thabitSigmaCriterion_seventyFive : ThabitSigmaCriterion 4 3 75 :=
  ⟨rfl, rfl⟩

/-- Subtraction-free form of the Thabit shape. -/
