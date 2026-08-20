/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The support of a nearest-neighbour bond gate sitting on the bond `i` of the
spin chain `ℤ`: the two sites `i` and `i + 1`. -/

lemma edge_subset_reach_cons {g : Gate N} {gs : List (Gate N)} {S : Set ℤ}
    (hd : ¬ Disjoint (edge g.bond) S) : edge g.bond ⊆ reach (g :: gs) S := by
  intro p hp
  exact Or.inr ⟨g, List.mem_cons_self, hd, hp⟩

/-- Conjugating an observable supported in `S` by a layer of gates keeps it
supported in the region reached from `S`. -/
