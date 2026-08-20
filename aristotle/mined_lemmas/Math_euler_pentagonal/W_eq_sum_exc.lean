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

theorem W_eq_sum_exc (n : ℕ) : W n = ∑ s ∈ (DP n).filter IsExc, (-1 : ℤ) ^ s.card := by
  have hzero : ∑ s ∈ (DP n).filter (fun s => ¬ IsExc s), (-1 : ℤ) ^ s.card = 0 := by
    refine Finset.sum_involution (fun s _ => franklin s) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact (franklin_spec (mem_DP.mp ha1).1 ha2).2.2.1
    · intro a ha _
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact (franklin_spec (mem_DP.mp ha1).1 ha2).2.2.2.1
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      obtain ⟨h0, hs⟩ := mem_DP.mp ha1
      obtain ⟨b1, b2, -, -, b5, -⟩ := franklin_spec h0 ha2
      exact Finset.mem_filter.mpr ⟨mem_DP.mpr ⟨b1, by rw [b2, hs]⟩, b5⟩
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact (franklin_spec (mem_DP.mp ha1).1 ha2).2.2.2.2.2
  rw [W, ← Finset.sum_filter_add_sum_filter_not (DP n) IsExc, hzero, add_zero]

