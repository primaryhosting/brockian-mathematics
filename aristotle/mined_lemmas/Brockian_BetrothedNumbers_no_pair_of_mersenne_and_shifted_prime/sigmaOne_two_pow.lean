/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁`. -/

lemma sigmaOne_two_pow (k : ℕ) : sigmaOne (2 ^ k) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp [sigmaOne]
  | succ n ih =>
      have hcalc : sigmaOne (2 ^ (n + 1)) = sigmaOne (2 ^ n) + 2 ^ (n + 1) := by
        simp only [sigmaOne, Nat.sum_divisors_prime_pow Nat.prime_two,
          Finset.sum_range_succ]
      rw [hcalc]
      have : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) := by ring
      omega

