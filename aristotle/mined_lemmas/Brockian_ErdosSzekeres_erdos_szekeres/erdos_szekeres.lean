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

theorem erdos_szekeres (r s : ℕ) (f : Fin (r * s + 1) → ℝ) (hf : Function.Injective f) :
    (∃ t : Finset (Fin (r * s + 1)), t.card = r + 1 ∧
        StrictMonoOn f ↑t) ∨
    (∃ t : Finset (Fin (r * s + 1)), t.card = s + 1 ∧
        StrictAntiOn f ↑t) := by
  have hn : r * s < Fintype.card (Fin (r * s + 1)) := by simp
  rcases erdos_szekeres_aux hn hf with ⟨t, ht, hmono⟩ | ⟨t, ht, hanti⟩
  · obtain ⟨t', ht's, ht'card⟩ := Finset.exists_subset_card_eq (show r + 1 ≤ #t from ht)
    exact Or.inl ⟨t', ht'card, hmono.mono (by exact_mod_cast Finset.coe_subset.2 ht's)⟩
  · obtain ⟨t', ht's, ht'card⟩ := Finset.exists_subset_card_eq (show s + 1 ≤ #t from ht)
    exact Or.inr ⟨t', ht'card, hanti.mono (by exact_mod_cast Finset.coe_subset.2 ht's)⟩

end Brockian.ErdosSzekeres

