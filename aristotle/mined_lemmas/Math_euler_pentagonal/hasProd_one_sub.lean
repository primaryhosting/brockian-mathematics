import Mathlib

/-!
# Franklin's involution

Combinatorial core of Euler's pentagonal number theorem: the signed count of partitions of
`n` into distinct parts (sign `(-1)^(number of parts)`) is `0` unless `n` is a generalized
pentagonal number.

Partitions into distinct parts are encoded as finite sets of positive naturals.
-/

namespace EulerPentagonal

open Finset

/-- The largest element of `s` (junk value `0` for `s = ∅`). -/

theorem hasProd_one_sub :
    HasProd (fun i : ℕ ↦ (1 - (X : ℤ⟦X⟧) ^ (i + 1))) (PowerSeries.mk W) := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  refine tendsto_atTop_of_eventually_const (i₀ := Finset.range d) (fun s hs => ?_)
  rw [coeff_prod_one_sub, sum_subsets_eq_W d s hs, coeff_mk]

/-- Euler's pentagonal series sums to the same power series. -/
