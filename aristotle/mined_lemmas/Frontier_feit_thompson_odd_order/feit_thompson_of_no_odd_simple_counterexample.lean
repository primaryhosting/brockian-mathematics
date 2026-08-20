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

theorem feit_thompson_of_no_odd_simple_counterexample :
    NoOddOrderSimpleCounterexample → FeitThompsonOddOrder :=
  fun h G _ _ hG => feit_thompson_odd_order h G hG

/-- Conversely, the full theorem trivially implies the simple case, so the reduction is an
equivalence. -/
