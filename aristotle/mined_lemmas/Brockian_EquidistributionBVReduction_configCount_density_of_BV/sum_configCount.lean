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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `S`:
the count of "configurations" of the first `N` terms of the sequence inside the window `S`. -/

lemma sum_configCount (x : ℕ → ℝ) (hk : 0 < k) (N : ℕ) :
    ∑ i ∈ Finset.range k, configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N = N := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun n => idx x k n) (s := Finset.range N) (t := Finset.range k)
    (fun n _ => idx_mem_range x hk n)
  simp only [Finset.card_range] at h
  refine (Finset.sum_congr rfl fun i _ => ?_).trans h.symm
  exact configCount_eq_card_fiber x hk i N

