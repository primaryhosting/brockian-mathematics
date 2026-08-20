import Mathlib
import RequestProject.ArrowImpossibility

/-!
# Arrow impossibility, phrased with `Fintype`

`RequestProject.ArrowImpossibility` is deliberately self-contained (it uses no imports at
all), so it expresses finiteness of the voter set by `Frontier.FinitelyMany`.  This file
records the same statement with Mathlib's `Fintype` hypothesis.
-/

namespace Frontier

universe v


theorem no_middle (huna : Unanimous F) (hiia : IIA F) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (P : V → Ranking (Fin 3))
    (hP : ∀ j, ((P j).lt b a ∧ (P j).lt b c) ∨ ((P j).lt a b ∧ (P j).lt c b)) :
    ¬ ((F P).lt a b ∧ (F P).lt b c) := by
  have hba : b ≠ a := hab.symm
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  have L4 := tri_lt_iff b c a hbc hba hca
  have L5 := tri_lt_iff c a b hca hcb hab
  rintro ⟨h1, h2⟩
  have hcase : ∀ j, ((P j).lt b a ∧ (P j).lt b c ∧ swapProfile a b c P j = tri b c) ∨
      ((P j).lt a b ∧ (P j).lt c b ∧ swapProfile a b c P j = tri c a) := by
    intro j
    rcases hP j with ⟨u, w⟩ | ⟨u, w⟩
    · exact Or.inl ⟨u, w, swapProfile_top u⟩
    · exact Or.inr ⟨u, w, swapProfile_bot ((P j).asym u)⟩
  have hab' : (F (swapProfile a b c P)).lt a b := by
    refine (iia_pair hiia _ P a b hab ?_).mpr h1
    intro j
    rcases hcase j with ⟨u, w, e⟩ | ⟨u, w, e⟩ <;> rw [e]
    · simp only [L4]
      have a1 : ¬ (P j).lt a b := (P j).asym u
      simp [hab, hac, hba, a1]
    · simp only [L5]
      simp [hac, hbc, u]
  have hbc' : (F (swapProfile a b c P)).lt b c := by
    refine (iia_pair hiia _ P b c hbc ?_).mpr h2
    intro j
    rcases hcase j with ⟨u, w, e⟩ | ⟨u, w, e⟩ <;> rw [e]
    · simp only [L4]
      simp [hbc, hca, hcb, w]
    · simp only [L5]
      have a2 : ¬ (P j).lt b c := (P j).asym w
      simp [hbc, hba, hcb, a2]
  have hcaF : (F (swapProfile a b c P)).lt c a := by
    refine huna _ c a ?_
    intro j
    rcases hcase j with ⟨u, w, e⟩ | ⟨u, w, e⟩ <;> rw [e]
    · simp only [L4]
      simp [hab, hcb]
    · simp only [L5]
      simp [hab, hac, hca]
  exact (F (swapProfile a b c P)).asym hcaF ((F (swapProfile a b c P)).tr hab' hbc')

/-- Extremal lemma: if every voter ranks `b` at the top or at the bottom, then so does
society. -/
