import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁`. -/

private theorem sum_range_two_pow (k : ℕ) : ∑ j ∈ range (k + 1), 2 ^ j = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      ring_nf
      omega

/-- `σ₁` of an odd prime times a power of two. -/
