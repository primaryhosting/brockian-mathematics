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

theorem hasSum_pentagonal :
    HasSum (fun k : ℤ ↦ ((-1 : ℤ) ^ k.natAbs) • (X : ℤ⟦X⟧) ^ pentN k) (PowerSeries.mk W) := by
  rw [WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  have hco : ∀ k : ℤ, (coeff d) (((-1 : ℤ) ^ k.natAbs) • (X : ℤ⟦X⟧) ^ pentN k)
      = if pentN k = d then ((-1 : ℤ) ^ k.natAbs) else 0 := by
    intro k
    rw [coeff_smul, coeff_X_pow]
    by_cases h : pentN k = d
    · rw [if_pos h.symm, if_pos h]; simp
    · rw [if_neg (fun hd => h hd.symm), if_neg h]; simp
  simp_rw [hco]
  rw [coeff_mk, W_eq d]
  refine hasSum_sum_of_ne_finset_zero ?_
  intro k hk
  simp only [Finset.mem_Icc, not_and, not_le] at hk
  by_cases h : pentN k = d
  · exfalso
    have hb := pentN_le k
    rw [h] at hb
    omega
  · rw [if_neg h]

/-- **Euler's pentagonal number theorem**:
`∏_{i ≥ 1} (1 - X^i) = ∑_{k ∈ ℤ} (-1)^k X^(k(3k-1)/2)` as formal power series over `ℤ`,
where the infinite product is the reciprocal of the generating function of the partition
function. -/
