/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment rather than a `/-!` module docstring, since Lean 4
-- requires `import` commands to precede every command, including module docstrings.)

import Mathlib

set_option maxHeartbeats 1000000

namespace Frontier

/-! ## Preferences

A *preference* on a type of alternatives `A` is a linear (total) order on `A`, presented as a
bundled relation.  This is the classical "ranked ballot" of social choice theory.
-/

/-- A ranking of the alternatives `A`: a total, transitive, antisymmetric relation. -/
structure Pref (A : Type*) where
  /-- The weak preference relation: `rel a b` means `a` is ranked at least as high as `b`. -/
  rel : A → A → Prop
  total' : ∀ a b, rel a b ∨ rel b a
  trans' : ∀ {a b c}, rel a b → rel b c → rel a c
  antisymm' : ∀ {a b}, rel a b → rel b a → a = b

namespace Pref

variable {A : Type*}

/-- Strict preference: `a` is ranked strictly above `b`. -/

def keyPref (key : A → ℤ) : Pref A where
  rel x y := key x < key y ∨ (key x = key y ∧ x ≤ y)
  total' := by
    intro a b
    rcases lt_trichotomy (key a) (key b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total a b with h2 | h2
      · exact Or.inl (Or.inr ⟨h, h2⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
    · exact Or.inr (Or.inl h)
  trans' := by
    rintro a b c (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, le_trans h1' h2'⟩
  antisymm' := by
    rintro a b (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · omega
    · omega
    · omega
    · exact le_antisymm h1' h2'

