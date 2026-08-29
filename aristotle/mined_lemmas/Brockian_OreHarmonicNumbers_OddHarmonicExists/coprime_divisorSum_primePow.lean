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

theorem coprime_divisorSum_primePow (hp : p.Prime) (k : ℕ) :
    Nat.Coprime (divisorSum (p ^ k)) p := by
  have hsplit : (∑ i ∈ range (k + 1), p ^ i)
      = 1 + (∑ i ∈ range k, p ^ i) * p := by
    rw [Finset.sum_range_succ']
    simp [Finset.sum_mul, pow_succ, Nat.add_comm]
  rw [divisorSum_primePow hp, hsplit]
  simp

/-- The sum of divisors of `p ^ k` is at least `1 + p ^ k`. -/
