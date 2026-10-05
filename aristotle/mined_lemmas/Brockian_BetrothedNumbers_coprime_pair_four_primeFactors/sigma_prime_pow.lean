/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- Geometric sum identity in `ℕ`, phrased so as to avoid truncated subtraction. -/

lemma sigma_prime_pow (p a : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]

/-- Key local bound: `σ(p^a) * (p-1) ≤ p^a * p`. -/
