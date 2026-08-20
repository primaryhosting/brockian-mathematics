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

lemma tendsto_configCount_Ico (x : ℕ → ℝ) (hequi : Equidistributed x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N => (configCount x (Set.Ico a b) N : ℝ) / N) atTop (𝓝 (b - a)) := by
  have h1 := hequi b ⟨le_trans ha hab, hb⟩
  have h2 := hequi a ⟨ha, le_trans hab hb⟩
  refine (h1.sub h2).congr (fun N => ?_)
  rw [configCount_split x ha hab N]
  push_cast
  ring

/-- The configuration count of `[i/m, (i+1)/m)` counts the fibre `⌊m * x n⌋₊ = i`. -/
