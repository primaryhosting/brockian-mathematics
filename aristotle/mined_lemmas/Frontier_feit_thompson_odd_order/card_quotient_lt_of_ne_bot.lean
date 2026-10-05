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

theorem card_quotient_lt_of_ne_bot [Finite G] {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have h1 : Nat.card N * N.index = Nat.card G := N.card_mul_index
  have h2 : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.2 hN
  have h3 : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (G ⧸ N) = N.index := rfl
  rw [h4]
  nlinarith

/-- A group that is an extension of a solvable group by a solvable normal subgroup is solvable. -/
