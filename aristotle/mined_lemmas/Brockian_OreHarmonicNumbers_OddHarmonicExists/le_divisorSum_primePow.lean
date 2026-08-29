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

theorem le_divisorSum_primePow (hp : p.Prime) (hk : 0 < k) :
    1 + p ^ k ≤ divisorSum (p ^ k) := by
  rw [divisorSum_primePow hp]
  have hsub : ({0, k} : Finset ℕ) ⊆ range (k + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  have hne : (0 : ℕ) ≠ k := by omega
  have h := Finset.sum_le_sum_of_subset (f := fun i => p ^ i) hsub
  simpa [Finset.sum_pair hne] using h

/-- No prime power `p ^ k` with `k ≥ 1` is an Ore harmonic number.  In particular an odd
Ore harmonic number greater than `1` cannot be a power of a single prime. -/
