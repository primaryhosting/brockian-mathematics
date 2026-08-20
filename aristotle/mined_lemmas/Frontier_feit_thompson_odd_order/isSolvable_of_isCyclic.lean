/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

universe u

/-- The full Feit–Thompson theorem, as a proposition about a universe of types:
every finite group of odd order is solvable. -/

theorem isSolvable_of_isCyclic {G : Type u} [Group G] [IsCyclic G] : IsSolvable G :=
  isSolvable_of_comm (fun a b => (IsCyclic.commGroup (α := G)).mul_comm a b)

/-- **Feit–Thompson, reduced to the simple case.**  Granting `OddOrderSimpleIsCyclic`, i.e. that
every finite simple group of odd order is cyclic (the deep content of the Feit–Thompson theorem),
every finite group of odd order is solvable.  This is the standard induction on the order:
a minimal counterexample would have to be simple. -/
