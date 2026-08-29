import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The statement of the Feit–Thompson (odd order) theorem: every finite group of odd
order is solvable. -/

def FeitThompsonStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → IsSolvable G

/-- The "simple case" of the Feit–Thompson theorem: every finite simple group of odd order
is abelian (equivalently, is cyclic of prime order). -/
