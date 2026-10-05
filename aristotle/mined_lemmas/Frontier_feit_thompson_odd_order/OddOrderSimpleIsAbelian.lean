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

def OddOrderSimpleIsAbelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Odd (Nat.card G) → IsSimpleGroup G →
    ∀ a b : G, a * b = b * a

section Auxiliary

variable {G : Type} [Group G]

/-- A group is solvable as soon as it has a normal subgroup `N` such that both `N` and `G ⧸ N`
are solvable. -/
