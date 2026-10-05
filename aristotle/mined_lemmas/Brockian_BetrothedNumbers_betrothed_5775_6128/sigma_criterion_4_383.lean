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

theorem sigma_criterion_4_383 :
    Nat.Prime 383 ∧ (383 : ℕ) ≠ 2 ∧ 2 ^ 4 * 383 = 6128 ∧
      (2 ^ (4 + 1) - 1) * (383 + 1) = 5775 + 6128 + 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Main result.**  `(5775, 6128)` is a betrothed (quasi-amicable) pair. -/
