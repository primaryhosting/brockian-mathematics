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
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Harmonic Exists
Category: Brockian Conjecture
Target: Brockian.OreHarmonicNumbers.OddHarmonicExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.OreHarmonicNumbers

/-- The sum of the divisors of `n`, usually written `σ n`. -/

theorem numDivisors_primePow (hp : p.Prime) (k : ℕ) :
    numDivisors (p ^ k) = k + 1 := by
  have h : ((p ^ k).divisors.card : ℕ) = ∑ _d ∈ (p ^ k).divisors, 1 := by
    simp
  rw [numDivisors, h, Nat.sum_divisors_prime_pow (f := fun _ => (1 : ℕ)) hp]
  simp

/-- The sum of divisors of `p ^ k` is coprime to `p`. -/
