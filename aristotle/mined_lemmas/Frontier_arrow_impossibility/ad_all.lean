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

lemma ad_all (hthree : ∀ x y : A, ∃ z : A, z ≠ x ∧ z ≠ y) {S : Finset V} {p q : A} (hpq : p ≠ q)
    (h : AlmostDecisive F S p q) : ∀ x y : A, x ≠ y → AlmostDecisive F S x y := by
  obtain ⟨t, htp, htq⟩ := hthree p q
  have hqp : AlmostDecisive F S q p := ad_swap hu hi hpq t htp htq h
  intro x y hxy
  by_cases hxp : x = p
  · subst hxp
    by_cases hyq : y = q
    · subst hyq; exact h
    · exact ad_expand_right hu hi hpq (Ne.symm hxy) hyq h
  · by_cases hxq : x = q
    · subst hxq
      by_cases hyp : y = p
      · subst hyp; exact hqp
      · exact ad_expand_right hu hi (Ne.symm hpq) (Ne.symm hxy) hyp hqp
    · by_cases hyq : y = q
      · subst hyq; exact ad_expand_left hu hi hpq hxp hxy h
      · by_cases hyp : y = p
        · subst hyp
          exact ad_expand_left hu hi (Ne.symm hpq) hxq hxy hqp
        · have h1 : AlmostDecisive F S p y := ad_expand_right hu hi hpq hyp hyq h
          exact ad_expand_left hu hi (Ne.symm hyp) hxp hxy h1

/-- Almost decisiveness for a single pair upgrades to full decisiveness. -/
