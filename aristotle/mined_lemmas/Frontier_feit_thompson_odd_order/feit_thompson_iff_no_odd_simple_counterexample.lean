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

theorem feit_thompson_iff_no_odd_simple_counterexample :
    FeitThompsonOddOrder ↔ NoOddOrderSimpleCounterexample :=
  ⟨fun h G _ _ _ hG => h G hG, feit_thompson_of_no_odd_simple_counterexample⟩

end Reduction

section BaseCases

/-- Base case: a group of prime power order is solvable (in particular any group of odd
prime power order). -/
