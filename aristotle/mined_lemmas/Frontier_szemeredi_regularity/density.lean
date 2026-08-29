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

noncomputable def density {α : Type*} (G : SimpleGraph α) (A B : Finset α) : ℝ :=
  (#{p ∈ A ×ˢ B | G.Adj p.1 p.2} : ℝ) / (#A * #B)

/-- A pair of vertex sets `(A, B)` is `ε`-regular for `G` when the density between any pair of
sufficiently large subsets `A' ⊆ A`, `B' ⊆ B` differs from the density between `A` and `B` by
less than `ε`. -/
