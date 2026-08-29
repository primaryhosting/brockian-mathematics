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

theorem feit_thompson_odd_order_of_large
    (h : ∀ (G : Type u) [Group G] [Finite G], IsSimpleGroup G → Odd (Nat.card G) →
      45 ≤ Nat.card G → ∀ a b : G, a * b = b * a) :
    OddOrderSolvable.{u} := by
  refine feit_thompson_odd_order fun G _ _ hs hodd => ?_
  by_cases hlt : Nat.card G < 45
  · have : IsSimpleGroup G := hs
    exact IsSimpleGroup.comm_iff_isSolvable.2 (feit_thompson_lt_45 hodd hlt)
  · exact h G hs hodd (not_lt.1 hlt)

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

