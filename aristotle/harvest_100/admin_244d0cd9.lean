/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import Archive.Wiedijk100Theorems.FriendshipGraphs

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- **The Friendship Theorem** (Erdős–Rényi–Sós).
If `G` is a finite, nonempty simple graph in which every two distinct vertices have exactly
one common neighbour ("every two people have exactly one common friend"), then some vertex is
adjacent to every other vertex ("someone is everyone's friend").

The proof invokes `Theorems100.friendship_theorem` from Mathlib's `Archive`
(`Archive/Wiedijk100Theorems/FriendshipGraphs.lean`). -/
theorem friendship_theorem {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hG : ∀ v w : V, v ≠ w → Nat.card (G.commonNeighbors v w) = 1) :
    ∃ v : V, ∀ w : V, w ≠ v → G.Adj v w := by
  classical
  have hG' : Theorems100.Friendship G := by
    intro v w hvw
    rw [← Nat.card_eq_fintype_card]
    exact hG v w hvw
  obtain ⟨v, hv⟩ := Theorems100.friendship_theorem hG'
  exact ⟨v, fun w hw => hv w (Ne.symm hw)⟩

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

