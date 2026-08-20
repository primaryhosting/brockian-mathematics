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

def FeitThompsonOddOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- The "no odd simple counterexample" hypothesis: every finite *simple* group of odd order
is solvable (equivalently, is cyclic of prime order). -/
