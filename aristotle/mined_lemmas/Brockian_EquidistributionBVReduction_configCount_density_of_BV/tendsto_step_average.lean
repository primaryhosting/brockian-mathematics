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

lemma tendsto_step_average (x : ℕ → ℝ) (hequi : Equidistributed x) (c : ℕ → ℝ) {m : ℕ}
    (hm : 0 < m) :
    Tendsto (fun N => (∑ i ∈ Finset.range m,
        c i * (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ)) / N)
      atTop (𝓝 (∑ i ∈ Finset.range m, c i / m)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hterm : ∀ i ∈ Finset.range m,
      Tendsto (fun N =>
          c i * ((configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ) / N))
        atTop (𝓝 (c i / m)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.1 hi
    have hi1 : (i:ℝ) + 1 ≤ m := by exact_mod_cast hi'
    have h := tendsto_configCount_Ico x hequi (a := (i:ℝ)/m) (b := ((i:ℝ)+1)/m)
      (by positivity) (by gcongr; linarith) (by rw [div_le_one hm']; exact hi1)
    have hlen : ((i:ℝ)+1)/m - (i:ℝ)/m = 1/m := by field_simp; ring
    rw [hlen] at h
    have h2 := h.const_mul (c i)
    simpa [mul_one_div] using h2
  have hsum := tendsto_finset_sum (Finset.range m) hterm
  refine hsum.congr (fun N => ?_)
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by rw [mul_div_assoc])

/-- Bounds for the integral of a monotone function over one subinterval of the partition. -/
