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

lemma configCount_eq_fiber_card (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) {m : ℕ}
    (hm : 0 < m) (N i : ℕ) :
    configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N
      = ((Finset.range N).filter (fun n => ⌊(m : ℝ) * x n⌋₊ = i)).card := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  unfold configCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Set.mem_Ico, and_congr_right_iff]
  intro _
  have h0 : (0:ℝ) ≤ (m:ℝ) * x n := mul_nonneg (le_of_lt hm') (hx n).1
  rw [Nat.floor_eq_iff h0, div_le_iff₀ hm', lt_div_iff₀ hm', mul_comm (x n) (m:ℝ)]

/-- Splitting a sum over `n < N` according to the fibres of `n ↦ ⌊m * x n⌋₊`. -/
