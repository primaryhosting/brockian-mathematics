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

theorem isBetrothedPair_of_sigma_criterion {k p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 0 < m) (hne : m ≠ 2 ^ k * p)
    (hsm : sigmaOne m = (2 ^ (k + 1) - 1) * (p + 1))
    (hsum : m + 2 ^ k * p + 1 = (2 ^ (k + 1) - 1) * (p + 1)) :
    IsBetrothedPair m (2 ^ k * p) := by
  refine ⟨hm, ?_, hne, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.two_pow_pos k) hp.pos
  · rw [hsm, hsum]
  · rw [sigmaOne_two_pow_mul_prime hp hp2, hsum]

/-- The pair `(5775, 6128)` arises from the `σ`-criterion with `k = 4`, `p = 383`:
`6128 = 2 ^ 4 * 383` with `383` prime, and `σ₁ 5775 = (2 ^ 5 - 1) * (383 + 1) = 5775 + 6128 + 1`. -/
