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

lemma ad_swap {S : Finset V} {a b : A} (hab : a ≠ b) (c : A) (hca : c ≠ a) (hcb : c ≠ b)
    (h : AlmostDecisive F S a b) : AlmostDecisive F S b a := by
  have h1 : AlmostDecisive F S c b := ad_expand_left hu hi hab hca hcb h
  have h2 : AlmostDecisive F S c a := ad_expand_right hu hi hcb (Ne.symm hca) hab h1
  exact ad_expand_left hu hi hca (Ne.symm hcb) (Ne.symm hab) h2

/-- Almost decisiveness for one pair implies almost decisiveness for every pair. -/
