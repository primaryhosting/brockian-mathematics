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

lemma prod_one_sub_expand (t : Finset ℕ) :
    ∏ i ∈ t, (1 - (X : ℤ⟦X⟧) ^ (i + 1))
      = ∑ u ∈ t.powerset, ((-1 : ℤ) ^ u.card) • (X : ℤ⟦X⟧) ^ (∑ i ∈ u, (i + 1)) := by
  have h : ∀ i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)) = (-(X : ℤ⟦X⟧) ^ (i + 1)) + 1 := by
    intro i; ring
  simp_rw [h]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp only [Finset.prod_const_one, mul_one]
  have h2 : ∀ i : ℕ, -(X : ℤ⟦X⟧) ^ (i + 1) = (-1 : ℤ⟦X⟧) * X ^ (i + 1) := by
    intro i; ring
  simp_rw [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  rw [zsmul_eq_mul]
  push_cast
  ring

