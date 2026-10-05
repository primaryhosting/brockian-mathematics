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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology Set

namespace Brockian.EquidistributionBVReduction

open scoped Classical in
/-- `configCount x A N` is the number of indices `n < N` whose orbit point `x n`,
reduced mod `1`, lands in the configuration set `A`. -/

lemma floor_mem_range (x : ℕ → ℝ) {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ∀ n ∈ Finset.range N, ⌊(K : ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range K := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  intro n _
  simp only [Finset.mem_range]
  rw [Nat.floor_lt (mul_nonneg hK'.le (Int.fract_nonneg _))]
  nlinarith [Int.fract_lt_one (x n), Int.fract_nonneg (x n)]

