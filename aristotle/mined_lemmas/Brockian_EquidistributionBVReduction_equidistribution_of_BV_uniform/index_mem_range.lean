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

import Mathlib

/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The frequency with which the fractional parts of the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/

lemma index_mem_range (x : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∀ n ∈ Finset.range N, ⌊(k : ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  intro n _
  have h0 : (0:ℝ) ≤ (k:ℝ) * Int.fract (x n) := mul_nonneg hk0.le (Int.fract_nonneg _)
  rw [Finset.mem_range, Nat.floor_lt h0]
  calc (k:ℝ) * Int.fract (x n) < k * 1 := by
        have := Int.fract_lt_one (x n)
        nlinarith
    _ = k := by ring

/-- Upper sandwich for a Birkhoff-type sum of a monotone function by the counting frequencies of
the uniform partition. -/
