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

lemma coeff_prod_one_sub (t : Finset ℕ) (d : ℕ) :
    (coeff d) (∏ i ∈ t, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      = ∑ u ∈ t.powerset.filter (fun u => ∑ i ∈ u, (i + 1) = d), (-1 : ℤ) ^ u.card := by
  rw [prod_one_sub_expand, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [coeff_smul, coeff_X_pow]
  by_cases h : ∑ i ∈ u, (i + 1) = d
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (fun hd => h hd.symm), if_neg h]; simp

/-- For `t ⊇ range d`, the signed count of subsets of `t` with weight `d` is `W d`. -/
