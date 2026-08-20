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

theorem thabit_abundant_iff_sigma {k p m : ℕ} (hm : m = (2 ^ k - 1) * (p + 2))
    (hs : sigma 1 m = m + 2 ^ k * p + 1) :
    2 * m < sigma 1 m ↔ 2 ^ (k + 1) < p + 3 := by
  have hid := thabit_balance_identity_sigma hm hs
  omega

/-- The betrothed pair `(48, 75)`: `σ(75) = 75 + 48 + 1`, of Thabit type with `k = 4`, `p = 3`. -/
