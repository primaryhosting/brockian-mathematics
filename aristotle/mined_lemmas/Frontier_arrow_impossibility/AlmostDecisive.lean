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

def AlmostDecisive (S : Finset V) (a b : A) : Prop :=
  ∀ P : V → Pref A, (∀ i ∈ S, (P i).lt a b) → (∀ i ∉ S, (P i).lt b a) → (F P).lt a b

/-- The coalition `S` is *decisive*: whenever its members prefer `x` to `y`, so does society,
no matter what the other voters think. -/
