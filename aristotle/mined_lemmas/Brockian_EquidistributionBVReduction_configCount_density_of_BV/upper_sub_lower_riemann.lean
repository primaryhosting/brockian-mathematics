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

lemma upper_sub_lower_riemann (f : ℝ → ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ i ∈ Finset.range m, f (((i : ℝ) + 1) / m) / m)
      - ∑ i ∈ Finset.range m, f ((i : ℝ) / m) / m = (f 1 - f 0) / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have htel := Finset.sum_range_sub (f := fun i : ℕ => f ((i:ℝ)/m)/m) m
  rw [← Finset.sum_sub_distrib]
  have hcongr : ∀ i ∈ Finset.range m,
      f (((i : ℝ) + 1) / m) / m - f ((i : ℝ) / m) / m
        = (fun i : ℕ => f ((i:ℝ)/m)/m) (i+1) - (fun i : ℕ => f ((i:ℝ)/m)/m) i := by
    intro i _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcongr, htel]
  simp [div_self (ne_of_gt hm')]
  ring

/-- Equidistribution implies convergence of Birkhoff-type averages for monotone weights. -/
