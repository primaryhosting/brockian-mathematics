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

/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d : ℕ}

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/

def IsPolitician {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∀ w : V, v ≠ w → G.Adj v w

section Basic

