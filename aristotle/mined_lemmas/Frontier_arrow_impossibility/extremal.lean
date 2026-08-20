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


theorem extremal (huna : Unanimous F) (hiia : IIA F) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (P : V → Ranking (Fin 3))
    (hP : ∀ j, ((P j).lt b a ∧ (P j).lt b c) ∨ ((P j).lt a b ∧ (P j).lt c b)) :
    ((F P).lt b a ∧ (F P).lt b c) ∨ ((F P).lt a b ∧ (F P).lt c b) := by
  have n1 := no_middle huna hiia hab hac hbc P hP
  have n2 := no_middle huna hiia (a := c) (b := b) (c := a) hbc.symm hac.symm hab.symm P
    (by
      intro j
      rcases hP j with ⟨u, w⟩ | ⟨u, w⟩
      · exact Or.inl ⟨w, u⟩
      · exact Or.inr ⟨w, u⟩)
  rcases (F P).tot b a hab.symm with hba | hab₂
  · rcases (F P).tot b c hbc with hbc₂ | hcb
    · exact Or.inl ⟨hba, hbc₂⟩
    · exact absurd ⟨hcb, hba⟩ n2
  · rcases (F P).tot b c hbc with hbc₂ | hcb
    · exact absurd ⟨hab₂, hbc₂⟩ n1
    · exact Or.inr ⟨hab₂, hcb⟩

/-- **Key lemma.** For any three distinct alternatives `a`, `b`, `c` there is a voter who
is decisive for the ordered pair `(a, c)`. -/
