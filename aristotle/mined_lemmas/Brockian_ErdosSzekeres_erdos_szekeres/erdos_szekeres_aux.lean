import Mathlib

/-!
# Erdős–Szekeres theorem

Any injective sequence of `r * s + 1` reals has a strictly increasing subsequence of length
`r + 1` or a strictly decreasing subsequence of length `s + 1`.

The proof is the classical pigeonhole argument: label each index `i` with the pair consisting of
the maximal length of an increasing subsequence ending at `i` and the maximal length of a
decreasing subsequence ending at `i`; these pairs are pairwise distinct, so if all increasing
sequences had length `≤ r` and all decreasing ones length `≤ s`, there would be at most `r * s`
indices.
-/

open Function Finset

namespace Brockian.ErdosSzekeres

section Aux

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β] {f : α → β} {i : α}

/-- The possible lengths of an increasing sequence which ends at `i`. -/
private noncomputable def incSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictMonoOn f t}

/-- The possible lengths of a decreasing sequence which ends at `i`. -/
private noncomputable def decSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictAntiOn f t}

/-- The singleton sequence is increasing, so 1 is a possible length. -/

private theorem erdos_szekeres_aux {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α)
    (hf : Injective f) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨
      ∃ t : Finset α, s < #t ∧ StrictAntiOn f t := by
  classical
  rsuffices ⟨i, hi⟩ : ∃ i, r < maxIncSequencesTo f i ∨ s < maxDecSequencesTo f i
  · refine Or.imp ?_ ?_ hi
    on_goal 1 =>
      have : maxIncSequencesTo f i ∈ image card _ := maxIncSequencesTo_mem
    on_goal 2 =>
      have : maxDecSequencesTo f i ∈ image card _ := maxDecSequencesTo_mem
    all_goals
      intro hi
      obtain ⟨t, ht₁, ht₂⟩ := mem_image.1 this
      refine ⟨t, by rwa [ht₂], ?_⟩
      rw [mem_filter] at ht₁
      exact ht₁.2.2
  by_contra! q
  have : Set.MapsTo (paired f) (univ : Finset α) (Icc 1 r ×ˢ Icc 1 s : Finset _) := by
    simp [paired, one_le_maxIncSequencesTo, one_le_maxDecSequencesTo, Set.MapsTo, *]
  refine hn.not_ge ?_
  simpa using card_le_card_of_injOn (paired f) this (paired_injective hf).injOn

end Aux

/-- Erdős–Szekeres: any sequence of r·s+1 distinct reals has a monotone subsequence of length
    r+1 (increasing) or s+1 (decreasing). -/
