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

lemma fiber_eq_filter_Ico (x : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (N j : ℕ) :
    ((Finset.range N).filter (fun n => ⌊(k : ℝ) * Int.fract (x n)⌋₊ = j)) =
      ((Finset.range N).filter
        (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  refine Finset.filter_congr (fun n _ => ?_)
  have h0 : (0:ℝ) ≤ (k:ℝ) * Int.fract (x n) := mul_nonneg hk0.le (Int.fract_nonneg _)
  rw [Nat.floor_eq_iff h0, Set.mem_Ico, div_le_iff₀ hk0, lt_div_iff₀ hk0]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith [h1], by linarith [h2]⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The indices `n < N` are distributed among the `k` subintervals of the uniform partition. -/
