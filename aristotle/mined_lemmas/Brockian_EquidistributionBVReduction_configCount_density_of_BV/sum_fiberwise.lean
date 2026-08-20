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

lemma sum_fiberwise (x : ℕ → ℝ) (hk : 0 < k) (N : ℕ) (F : ℕ → ℝ) :
    ∑ i ∈ Finset.range k, ∑ n ∈ (Finset.range N).filter (fun n => idx x k n = i), F n
      = ∑ n ∈ Finset.range N, F n :=
  Finset.sum_fiberwise_of_maps_to (fun n _ => idx_mem_range x hk n) F

/-- Lower Riemann sum bound for a monotone integrand. -/
