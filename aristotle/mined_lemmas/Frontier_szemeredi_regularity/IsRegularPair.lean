import Mathlib

/-!
# Szemeredi Regularity
Category: Frontier Abel
Target: Frontier.szemeredi_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset

/-- The edge density of a graph `G` between two finite sets of vertices `A` and `B`: the
proportion of pairs in `A × B` that are adjacent. -/

def IsRegularPair {α : Type*} (G : SimpleGraph α) (ε : ℝ) (A B : Finset α) : Prop :=
  ∀ A' ⊆ A, ∀ B' ⊆ B, ε * #A ≤ #A' → ε * #B ≤ #B' →
    |density G A' B' - density G A B| < ε

/-- `Frontier.density` agrees with Mathlib's `SimpleGraph.edgeDensity`. -/
