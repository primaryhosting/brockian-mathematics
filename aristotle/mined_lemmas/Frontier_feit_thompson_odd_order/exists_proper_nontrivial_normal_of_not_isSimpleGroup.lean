import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


universe u'

namespace Frontier

/-- The Feit–Thompson odd order theorem, as a proposition: every finite group of odd order
is solvable. -/

theorem exists_proper_nontrivial_normal_of_not_isSimpleGroup
    (G : Type*) [Group G] [Nontrivial G] (h : ¬ IsSimpleGroup G) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hc
  push_neg at hc
  refine h { eq_bot_or_eq_top_of_normal := fun H hH => ?_ }
  rcases eq_or_ne H ⊥ with hb | hb
  · exact Or.inl hb
  · exact Or.inr (hc H hH hb)

/-- Induction step packaged as a bounded statement, for strong induction on the order. -/
