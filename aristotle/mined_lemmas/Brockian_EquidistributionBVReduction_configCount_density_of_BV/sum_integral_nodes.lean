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

lemma sum_integral_nodes (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, ∫ t in ((i : ℝ) / k)..(((i : ℝ) + 1) / k), g t
      = ∫ t in (0 : ℝ)..1, g t := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := fun i : ℕ => (i : ℝ) / k) (n := k) (by
      intro i hi
      have := intervalIntegrable_node hg hk hi
      push_cast
      exact this)
  simpa [div_self (ne_of_gt hk')] using this

