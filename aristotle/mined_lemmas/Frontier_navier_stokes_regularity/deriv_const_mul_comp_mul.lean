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

theorem deriv_const_mul_comp_mul {g : ℝ → ℝ} (hg : Differentiable ℝ g) (c a t : ℝ) :
    deriv (fun s => c * g (a * s)) t = c * a * deriv g (a * t) := by
  have h1 : HasDerivAt (fun s : ℝ => a * s) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have h2 : HasDerivAt (fun s : ℝ => g (a * s)) (deriv g (a * t) * a) t :=
    (hg (a * t)).hasDerivAt.comp t h1
  rw [(h2.const_mul c).deriv]
  ring

