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

def NoOddOrderSimpleCounterexample : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → Odd (Nat.card G) → IsSolvable G

section Reduction


/-- A divisor of an odd natural number is odd. -/
