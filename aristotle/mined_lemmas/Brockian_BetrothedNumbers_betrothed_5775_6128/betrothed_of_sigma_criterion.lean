/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ArithmeticFunction.sigma

set_option maxRecDepth 100000

namespace Brockian.BetrothedNumbers

/-- Two distinct positive naturals `m ≠ n` form a *betrothed* (quasi-amicable) pair when
each is the sum of the *nontrivial* proper divisors of the other, equivalently
`σ m = σ n = m + n + 1`. -/

lemma betrothed_of_sigma_criterion {k p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 0 < m)
    (hne : m ≠ 2 ^ k * p)
    (hsum : m + 2 ^ k * p + 1 = (2 ^ (k + 1) - 1) * (p + 1))
    (hsig : σ 1 m = (2 ^ (k + 1) - 1) * (p + 1)) :
    IsBetrothedPair m (2 ^ k * p) := by
  refine ⟨hm, ?_, hne, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.two_pow_pos k) hp.pos
  · rw [hsig, hsum]
  · rw [sigma_one_two_pow_mul_prime hp hp2, hsum]

/-- `σ 5775 = 11904`, verified by kernel computation of the divisor sum. -/
