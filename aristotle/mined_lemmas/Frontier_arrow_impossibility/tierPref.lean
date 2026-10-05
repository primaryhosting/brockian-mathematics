/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- A strict preference relation on the set of alternatives `A`: a strict linear order,
given by a transitive, trichotomous, irreflexive relation. -/
structure StrictPref (A : Type*) where
  lt : A → A → Prop
  trans' : ∀ {x y z : A}, lt x y → lt y z → lt x z
  trichotomous' : ∀ x y : A, lt x y ∨ x = y ∨ lt y x
  irrefl' : ∀ x : A, ¬ lt x x

namespace StrictPref

variable {A : Type*}


noncomputable def tierPref (t : A → ℕ) : StrictPref A where
  lt x y := t x < t y ∨ (t x = t y ∧ WellOrderingRel x y)
  trans' := by
    rintro x y z (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩)
    · exact Or.inl (lt_trans h h')
    · exact Or.inl (h1' ▸ h)
    · exact Or.inl (h1 ▸ h')
    · exact Or.inr ⟨h1.trans h1', Trans.trans h2 h2'⟩
  trichotomous' := by
    intro x y
    rcases lt_trichotomy (t x) (t y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases trichotomous_of (WellOrderingRel (α := A)) x y with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
    · exact Or.inr (Or.inr (Or.inl h))
  irrefl' := by
    rintro x (h | ⟨-, h⟩)
    · exact lt_irrefl _ h
    · exact irrefl_of _ _ h

/-- The preference which ranks `x` first, `y` second, `z` third, and all other
alternatives below. -/
