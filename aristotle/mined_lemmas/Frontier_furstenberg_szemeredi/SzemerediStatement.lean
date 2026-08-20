/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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

/-- The counting function of a set of naturals: the number of elements of `A` below `n`. -/

def SzemerediStatement : Prop :=
  ∀ A : Set ℕ, 0 < upperDensity A → ∀ k : ℕ, HasAPOfLength A k

/-- The finitary form of Szemerédi's theorem: for every length `k` and density `ε > 0` there is
an `N` such that every subset of `{0, …, n-1}` with `n ≥ N` and at least `ε n` elements contains
an arithmetic progression of length `k`. -/
