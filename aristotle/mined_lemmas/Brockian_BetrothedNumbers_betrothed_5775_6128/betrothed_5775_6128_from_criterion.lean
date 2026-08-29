import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`.  It agrees with Mathlib's
`ArithmeticFunction.sigma 1` (see `sigmaOne_eq`). -/

theorem betrothed_5775_6128_from_criterion :
    IsBetrothedPair 5775 (2 ^ 4 * 383) ∧ Nat.Prime 383 ∧
      sigmaOne (2 ^ 4 * 383) = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      (2 ^ (4 + 1) - 1) * (383 + 1) = 5775 + 6128 + 1 := by
  refine ⟨by simpa using betrothed_5775_6128, by norm_num, ?_, by norm_num⟩
  exact sigmaOne_two_pow_mul_prime (by norm_num) (by norm_num)

/-- A second, purely computational proof of the main result: both sigma values are
kernel-verified by `decide`. -/
