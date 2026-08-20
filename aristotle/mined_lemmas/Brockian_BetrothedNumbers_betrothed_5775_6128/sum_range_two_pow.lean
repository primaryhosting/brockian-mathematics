import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.BetrothedNumbers

open Finset

set_option maxRecDepth 100000

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

private theorem sum_range_two_pow (n : ℕ) : (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; omega

/-- The sigma value of `2 ^ k * p` for an odd prime `p`. -/
