/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Finset MeasureTheory Metric Module Real Set

/-! ## The Pfaffian of the curvature form of the unit round sphere -/

section Pfaffian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- First index of the `i`-th pair `(2i, 2i+1)`. -/

theorem pairProd_perm (m : ℕ) (v : Fin (2 * m) → V) (σ : Equiv.Perm (Fin (2 * m))) :
    pairProd m (v ∘ σ) = (Equiv.Perm.sign σ : ℝ) • ExteriorAlgebra.ιMulti ℝ (2 * m) v := by
  rw [pairProd_eq_ιMulti, AlternatingMap.map_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **The Pfaffian of the curvature form of the unit round sphere.**
For the round sphere `S^{2m}` of radius one, the curvature two-forms in an orthonormal coframe
`v` are `Ω i j = v i ∧ v j`, and the Pfaffian of `Ω` equals `(2m)! / (2^m m!)` times the
volume form `v 0 ∧ ⋯ ∧ v (2m-1)`. -/
