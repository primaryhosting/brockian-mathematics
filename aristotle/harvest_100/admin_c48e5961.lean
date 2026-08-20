/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import Archive.Wiedijk100Theorems.FriendshipGraphs

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open SimpleGraph

/-- **The Friendship Theorem** (Erdős–Rényi–Sós): in a finite nonempty simple graph in which
every two distinct vertices have exactly one common neighbour ("every two people have exactly
one common friend"), there is a vertex adjacent to all others ("someone is everyone's friend").

The proof is by `Theorems100.friendship_theorem` from Mathlib's Archive
(`Archive/Wiedijk100Theorems/FriendshipGraphs.lean`). -/
theorem friendship_theorem {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hG : ∀ ⦃v w : V⦄, v ≠ w → (G.commonNeighbors v w).ncard = 1) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  classical
  refine Theorems100.friendship_theorem (G := G) (fun v w hvw => ?_)
  have := hG hvw
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at this
  convert this using 2

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

