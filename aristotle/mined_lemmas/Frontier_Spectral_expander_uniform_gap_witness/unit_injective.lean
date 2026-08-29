import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`
(there are `2 ^ k` of them). -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2


theorem unit_injective {k : ℕ} : Function.Injective (unit (k := k)) := by
  intro i j h
  by_contra hne
  have := congrFun h i
  simp [unit, hne] at this

/-- The hypercube graph `Q k`: two bit strings are adjacent when one is obtained from the
other by flipping a single bit (equivalently, when they differ in exactly one coordinate;
see `hypercube_adj_iff`). -/
