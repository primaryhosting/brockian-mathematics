import Mathlib

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

/-
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- `sigmaOne n` is the sum of all divisors of `n`. -/

lemma odd_sigmaOne_prime_pow_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    Odd (sigmaOne (p ^ k)) ↔ Even k := by
  have key : sigmaOne (p ^ k) % 2 = (k + 1) % 2 := by
    unfold sigmaOne
    rw [Nat.sum_divisors_prime_pow hp, Finset.sum_nat_mod]
    rw [Finset.sum_congr rfl (fun i _ => Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow (n := i)))]
    simp
  rw [Nat.odd_iff, Nat.even_iff, key]
  omega

/-- If `σ(n)` is odd then every odd prime occurs to an even power in `n`. -/
