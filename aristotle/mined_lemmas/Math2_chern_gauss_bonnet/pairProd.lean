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

noncomputable def pairProd (m : ℕ) (v : Fin (2 * m) → V) : ExteriorAlgebra ℝ V :=
  (List.ofFn fun i : Fin m => curvForm v (pairFst m i) (pairSnd m i)).prod

/-- The Pfaffian of the curvature form of the unit round sphere `S^{2m}`, computed in an
orthonormal coframe `v`:
`Pf(Ω) = (2^m m!)⁻¹ ∑_{σ ∈ S_{2m}} sgn(σ) Ω_{σ(0)σ(1)} ∧ ⋯ ∧ Ω_{σ(2m-2)σ(2m-1)}`. -/
