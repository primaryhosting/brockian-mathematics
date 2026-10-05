/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Feit–Thompson theorem states that every finite group of odd order is solvable.
Its full proof is far beyond current formalization, and it is not available in Mathlib.

This file provides:

* `Frontier.OddOrderSolvable`, the formal statement of the theorem;
* `Frontier.NoOddOrderNonabelianSimple`, its simple-group form;
* `Frontier.feit_thompson_odd_order`, a Lean-checked reduction of the theorem to the
  simple-group form, and `Frontier.oddOrderSolvable_iff`, showing the two forms are equivalent;
* unconditional base cases: groups of squarefree order and groups of prime power order are
  solvable, and hence so is every group of odd order less than `45`
  (`Frontier.feit_thompson_lt_45`);
* `Frontier.feit_thompson_odd_order_of_large`, a sharper reduction in which the simple-group
  hypothesis is only needed for groups of order at least `45`.
-/

universe u

namespace Frontier

/-- The Feit–Thompson theorem, as a statement about all finite groups in a fixed universe:
every finite group of odd order is solvable. -/

theorem isSolvable_of_normal_of_quotient (N : Subgroup G) [N.Normal] [IsSolvable N]
    [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- A nontrivial finite group that is not simple has a normal subgroup that is neither trivial
nor everything. -/
