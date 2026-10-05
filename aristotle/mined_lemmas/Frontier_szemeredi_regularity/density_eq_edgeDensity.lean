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

theorem density_eq_edgeDensity {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (A B : Finset α) :
    density G A B = ((G.edgeDensity A B : ℚ) : ℝ) := by
  simp only [density, SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def]
  push_cast
  refine congrArg (fun n : ℕ => (n : ℝ) / ((#A : ℝ) * (#B : ℝ))) ?_
  congr

/-- `Frontier.IsRegularPair` agrees with Mathlib's `SimpleGraph.IsUniform` over `ℝ`. -/
