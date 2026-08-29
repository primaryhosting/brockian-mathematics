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

theorem isSolvable_of_normal_subgroup (N : Subgroup G) [N.Normal] [IsSolvable N]
    [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.subtype_range])

/-- A nontrivial proper normal subgroup of a finite group has strictly smaller cardinality. -/
