import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/

lemma lapMatrix_cycle_mulVec (R : Type*) [NonAssocRing R] (x : Fin (m + 3) → R)
    (v : Fin (m + 3)) :
    ((cycleGraph (m + 3)).lapMatrix R *ᵥ x) v = 2 * x v - x (v - 1) - x (v + 1) := by
  have hne : v - 1 ≠ v + 1 := by
    intro h
    have h2 : ({v - 1, v + 1} : Finset (Fin (m + 3))).card = 2 := by
      rw [← cycleGraph_neighborFinset]
      exact cycleGraph_degree_three_le
    rw [h] at h2
    simp at h2
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
    Finset.sum_pair hne]
  push_cast
  rw [sub_sub]

