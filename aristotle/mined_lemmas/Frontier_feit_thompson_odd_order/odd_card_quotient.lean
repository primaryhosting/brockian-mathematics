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

theorem odd_card_quotient [Finite G] (hodd : Odd (Nat.card G)) (N : Subgroup G) [N.Normal] :
    Odd (Nat.card (G ⧸ N)) :=
  hodd.of_dvd_nat (by rw [← Subgroup.index]; exact N.index_dvd_card)

/-- A proper subgroup of a finite group has strictly smaller cardinality. -/
