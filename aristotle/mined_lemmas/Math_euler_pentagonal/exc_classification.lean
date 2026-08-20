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

lemma exc_classification {s : Finset ℕ} (h0 : 0 ∉ s) (hexc : IsExc s) : ∃ k : ℤ, s = excSet k := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · exact ⟨0, by simp [excSet]⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := basic_facts h0 hne
  by_cases hle : mn s ≤ sl s
  · rw [IsExc, if_pos hle] at hexc
    have hsl : sl s = mn s := by omega
    have hs : s = Finset.Icc (mn s) (mx s) := eq_Icc_of (fun x hx1 hx2 => by omega)
    refine ⟨(mn s : ℤ), ?_⟩
    have hcast : ((mn s : ℤ)).natAbs = mn s := by simp
    rw [excSet, if_pos (by omega), hcast, ← hexc]
    exact hs
  · rw [IsExc, if_neg hle] at hexc
    have hmn : mn s = sl s + 1 := by omega
    have hs : s = Finset.Icc (mn s) (mx s) := eq_Icc_of (fun x hx1 hx2 => by omega)
    refine ⟨-(sl s : ℤ), ?_⟩
    have hcast : ((-(sl s : ℤ))).natAbs = sl s := by simp
    rw [excSet, if_neg (by omega), if_pos (by omega), hcast, ← hexc, ← hmn]
    exact hs

/-- Partitions of `n` into distinct parts, encoded as sets of positive integers. -/
