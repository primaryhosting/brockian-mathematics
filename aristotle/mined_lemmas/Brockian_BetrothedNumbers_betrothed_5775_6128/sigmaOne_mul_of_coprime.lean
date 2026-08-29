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

lemma sigmaOne_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigmaOne (a * b) = sigmaOne a * sigmaOne b := by
  simp only [sigmaOne_eq]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

/-- `σ₁(2 ^ k) = 2 ^ (k+1) - 1`. -/
