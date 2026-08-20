import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma geom_sum_mul_succ (q a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), (q + 1) ^ i) * q + 1 = (q + 1) ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Finset.sum_range_succ, add_mul, pow_succ ((q+1)) (a+1)]
      nlinarith [ih]

/-- `σ (p ^ a) * (p - 1) < p ^ a * p` for a prime `p`. -/
