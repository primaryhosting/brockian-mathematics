/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

universe u

/-- The full Feit–Thompson theorem, as a proposition about a universe of types:
every finite group of odd order is solvable. -/

theorem exists_proper_normal_of_not_simple {G : Type u} [Group G] [Nontrivial G]
    (h : ¬ IsSimpleGroup G) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hc
  push_neg at hc
  exact h { exists_pair_ne := exists_pair_ne G
            eq_bot_or_eq_top_of_normal := fun N hN => by
              by_cases hb : N = ⊥
              · exact Or.inl hb
              · exact Or.inr (hc N hN hb) }

/-- A cyclic group is solvable. -/
