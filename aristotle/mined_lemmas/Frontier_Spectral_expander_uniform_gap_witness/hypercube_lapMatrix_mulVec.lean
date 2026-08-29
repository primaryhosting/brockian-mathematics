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

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2

/-- The basis vector flipping coordinate `i`. -/

lemma hypercube_lapMatrix_mulVec (k : ℕ) (v : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ *ᵥ v) x = k * v x - ∑ i, v (x + flip i) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, hypercube_degree, hypercube_neighborFinset,
    Finset.sum_image]
  intro i _ j _ h
  exact flip_injective (by simpa using h)

/-! ### Characters of the hypercube -/

/-- The sign character of `ZMod 2`. -/
