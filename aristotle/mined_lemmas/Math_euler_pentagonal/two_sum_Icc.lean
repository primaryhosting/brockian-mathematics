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

lemma two_sum_Icc (a b : ℕ) (hab : a ≤ b + 1) :
    2 * (∑ x ∈ Finset.Icc a b, x) + a * (a - 1) = (b + 1) * b := by
  have hsub : Finset.range a ⊆ Finset.range (b + 1) :=
    Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))
  have h1 : Finset.Icc a b = Finset.range (b + 1) \ Finset.range a := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range, not_lt]
    omega
  have h2 := Finset.sum_sdiff (f := fun i => i) hsub
  have h3 := Finset.sum_range_id_mul_two a
  have h4 := Finset.sum_range_id_mul_two (b + 1)
  rw [h1]
  simp only [Nat.add_sub_cancel] at h4
  linarith

/-- The `k`-th generalized pentagonal number `k(3k-1)/2`, as a natural number. -/
