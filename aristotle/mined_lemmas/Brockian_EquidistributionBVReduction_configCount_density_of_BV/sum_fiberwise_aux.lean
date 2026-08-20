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

import Brockian.EquidistributionBVReduction

/-!
# An equidistributed sequence

This file exhibits a concrete sequence in `[0,1)` satisfying
`Brockian.EquidistributionBVReduction.Equidistributed`, showing that the equidistribution
hypothesis of `configCount_density_of_BV` is satisfiable (so the theorem is not vacuous).

The sequence is the "triangular block" sequence: the `k`-th block lists the `k+1` points
`0/(k+1), 1/(k+1), …, k/(k+1)`.
-/

open Filter Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- Start index of block `k`; block `k` consists of the `k+1` indices
`blockStart k, …, blockStart k + k`. -/

lemma sum_fiberwise_aux (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (g : ℕ → ℝ) {m : ℕ}
    (hm : 0 < m) (N : ℕ) :
    ∑ n ∈ Finset.range N, g n
      = ∑ i ∈ Finset.range m,
          ∑ n ∈ (Finset.range N).filter (fun n => ⌊(m:ℝ) * x n⌋₊ = i), g n := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
  intro n _
  simp only [Finset.mem_range]
  rw [Nat.floor_lt (mul_nonneg hm'.le (hx n).1)]
  calc (m:ℝ) * x n < (m:ℝ) * 1 := by nlinarith [(hx n).2]
    _ = m := by ring

/-- Lower Riemann-type bound on the sum of `f (x n)`. -/
