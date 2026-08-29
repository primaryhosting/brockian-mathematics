/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ContDiff

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Basic differential operators on `ℝ³` -/

/-- Physical space `ℝ³`. -/
abbrev Vec3 : Type := Fin 3 → ℝ

/-- The partial derivative `∂f/∂xᵢ` of a scalar field on `ℝ³`. -/

def SatisfiesNSEquations (ν : ℝ) (u : ℝ → Vec3 → Vec3) (p : ℝ → Vec3 → ℝ) : Prop :=
  (∀ t x, divergence (u t) x = 0) ∧
    (∀ (t : ℝ) (x : Vec3) (j : Fin 3),
      deriv (fun s => u s x j) t + ∑ i, u t x i * partialDeriv i (fun y => u t y j) x
        = ν * laplacian (fun y => u t y j) x - partialDeriv j (p t) x)

