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

lemma franklin_spec {s : Finset ℕ} (h0 : 0 ∉ s) (hexc : ¬ IsExc s) :
    0 ∉ franklin s ∧ (∑ i ∈ franklin s, i) = ∑ i ∈ s, i ∧
      ((-1 : ℤ) ^ s.card + (-1) ^ (franklin s).card = 0) ∧ franklin s ≠ s ∧
      ¬ IsExc (franklin s) ∧ franklin (franklin s) = s := by
  have hne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exact absurd isExc_empty hexc
    · exact h
  by_cases hle : mn s ≤ sl s
  · obtain ⟨a1, -, a3, a4, a5, a6⟩ := caseA h0 hne hle hexc
    refine ⟨a1, a3, ?_, ?_, a5, a6⟩
    · rw [← a4, pow_succ]; ring
    · intro h; rw [h] at a4; omega
  · obtain ⟨a1, -, a3, a4, a5, a6⟩ := caseB h0 hne hle hexc
    refine ⟨a1, a3, ?_, ?_, a5, a6⟩
    · rw [a4, pow_succ]; ring
    · intro h; rw [h] at a4; omega

