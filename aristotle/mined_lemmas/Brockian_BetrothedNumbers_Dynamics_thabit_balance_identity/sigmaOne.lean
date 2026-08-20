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

def sigmaOne (n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun d => d != 0 && n % d == 0)).sum

/-- The **Thabit sigma criterion** for a Thabit-type betrothed (quasi-amicable) configuration:
`m` has the Thabit shape `(2 ^ k - 1) * (p + 2)` and satisfies the betrothed relation
`σ(m) = m + n + 1` with partner `n = 2 ^ k * p`. -/
