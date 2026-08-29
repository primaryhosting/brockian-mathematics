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
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Math2.Defs

/-!
Elementary finite-probability toolkit for `p`-random subsets: the expectation `Ex p f`,
the fact that the weights sum to one, and the "union of independent random sets" identity.
-/

namespace Math2

open Finset

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The expectation of `f` at a `p`-random subset of the ground set `s`. -/

lemma mcost_empty (hp : 0 ≤ p) : mcost p (∅ : Finset (Finset X)) = 0 := by
  refine le_antisymm ?_ (mcost_nonneg hp _)
  have h : Covers (∅ : Finset (Finset X)) (∅ : Finset (Finset X)) := by
    intro S hS; simp at hS
  simpa [cost] using mcost_le_cost (p := p) h

