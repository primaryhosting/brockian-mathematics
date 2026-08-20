import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The sum of all (positive) divisors of `n`, i.e. `σ₁ n`. -/

lemma sigmaSum_two_pow (k : ℕ) : sigmaSum (2 ^ k) = 2 ^ (k + 1) - 1 := by
  unfold sigmaSum
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 2 ≤ 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
      ring_nf
      omega

/-- `σ₁ (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1)` for an odd prime `p`. -/
