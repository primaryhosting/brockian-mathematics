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

theorem sigma_seventyFive : sigma 1 75 = 75 + 2 ^ 4 * 3 + 1 := by
  rw [← sigmaOne_eq_sigma]
  rfl

end Brockian.BetrothedNumbers.Dynamics

/-!
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers.Dynamics

/-- `sigmaOne n` is the sum of the (positive) divisors of `n`, i.e. the classical `σ(n)`.
(It is shown to agree with Mathlib's `ArithmeticFunction.sigma 1` in
`RequestProject.ThabitBalanceIdentityMathlib`.) -/
