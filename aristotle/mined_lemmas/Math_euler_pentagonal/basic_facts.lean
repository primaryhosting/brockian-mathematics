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

lemma basic_facts {s : Finset ℕ} (h0 : 0 ∉ s) (hne : s.Nonempty) :
    1 ≤ mn s ∧ mn s ≤ mx s ∧ 1 ≤ sl s ∧ sl s ≤ mx s ∧ mn s + sl s ≤ mx s + 1 := by
  have hm := mn_mem hne
  have hM := mx_mem hne
  have h1 : 1 ≤ mn s := by
    rcases Nat.eq_zero_or_pos (mn s) with h | h
    · exact absurd (h ▸ hm) h0
    · exact h
  have h2 : mn s ≤ mx s := mn_le hM
  have h3 : 1 ≤ sl s := by
    rcases Nat.eq_zero_or_pos (sl s) with h | h
    · exact absurd hM (by simpa [h] using sl_notMem h0)
    · exact h
  have h4 : sl s ≤ mx s := by
    by_contra h
    push_neg at h
    have := mem_of_lt_sl (s := s) (i := mx s) h
    simp only [Nat.sub_self] at this
    exact h0 this
  have h5 : mn s + sl s ≤ mx s + 1 := by
    have := mn_le (mem_of_lt_sl (s := s) (i := sl s - 1) (by omega))
    omega
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Franklin's map. -/
