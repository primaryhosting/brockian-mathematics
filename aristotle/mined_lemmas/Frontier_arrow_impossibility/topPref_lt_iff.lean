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

lemma topPref_lt_iff {z : A} {p : Pref A} {x y : A} (hx : x ≠ z) (hy : y ≠ z) :
    (topPref z p).lt x y ↔ p.lt x y := by
  rw [Pref.lt_iff, Pref.lt_iff]
  constructor
  · intro h h2
    exact h (Or.inr ⟨hx, h2⟩)
  · rintro h (rfl | ⟨-, h2⟩)
    · exact hy rfl
    · exact h h2

end Constructions

/-! ## Social welfare functions and Arrow's axioms -/

section Axioms

variable {V A : Type*}

/-- A social welfare function aggregates a profile of individual rankings into a social ranking. -/
abbrev SWF (V A : Type*) := (V → Pref A) → Pref A

/-- Unanimity (weak Pareto): if every voter strictly prefers `a` to `b`, so does society. -/
