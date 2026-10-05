import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Rankings -/

/-- A strict linear ranking (irreflexive, transitive, total) of the alternatives `A`.
`R.rel a b` means "`a` is strictly preferred to `b`". -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {a b c : A}, rel a b → rel b c → rel a c
  rel_irrefl : ∀ a : A, ¬ rel a a
  rel_total : ∀ a b : A, a ≠ b → rel a b ∨ rel b a

namespace Ranking

variable {A : Type*}


noncomputable def scoreRanking {A : Type*} (s : A → ℕ) : Ranking A where
  rel a b := s a < s b ∨ (s a = s b ∧ WellOrderingRel a b)
  rel_trans := by
    rintro a b c (h1 | ⟨h1, w1⟩) (h2 | ⟨h2, w2⟩)
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, _root_.trans w1 w2⟩
  rel_irrefl := by
    rintro a (h | ⟨-, w⟩)
    · exact lt_irrefl _ h
    · exact irrefl_of WellOrderingRel a w
  rel_total := by
    intro a b hab
    rcases lt_trichotomy (s a) (s b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases trichotomous_of WellOrderingRel a b with w | w | w
      · exact Or.inl (Or.inr ⟨h, w⟩)
      · exact absurd w hab
      · exact Or.inr (Or.inr ⟨h.symm, w⟩)
    · exact Or.inr (Or.inl h)

