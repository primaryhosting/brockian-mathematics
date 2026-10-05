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

lemma geom_sum_mul_succ (q a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), (q + 1) ^ i) * q + 1 = (q + 1) ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Finset.sum_range_succ, add_mul]
      have : (q + 1) ^ (a + 1 + 1) = (q + 1) ^ (a + 1) * q + (q + 1) ^ (a + 1) := by ring
      omega

/-- The sum of divisors of a prime power. -/
