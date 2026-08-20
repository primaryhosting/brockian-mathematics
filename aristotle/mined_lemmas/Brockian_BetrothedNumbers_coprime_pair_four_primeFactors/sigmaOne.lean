/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

/-- `σ₁ n` is the sum of divisors of `n`. -/

noncomputable def sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- A pair `(m, n)` of positive integers is *betrothed* (quasi-amicable) when the sum of the
divisors of each of them equals `m + n + 1`. -/
