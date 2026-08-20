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

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

noncomputable def scaledSchwartz (c : ℝ) (hc : 0 < c) (U : SchwartzMap E3 E3) :
    SchwartzMap E3 E3 :=
  c • (SchwartzMap.compCLM (g := fun x : E3 => c • x) ℝ
    ((c • ContinuousLinearMap.id ℝ E3).hasTemperateGrowth)
    ⟨1, c⁻¹, by
      intro x
      have hnorm : ‖c • x‖ = c * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      rw [hnorm, pow_one]
      have h1 : ‖x‖ = c⁻¹ * (c * ‖x‖) := by rw [inv_mul_cancel_left₀ hc.ne']
      nlinarith [norm_nonneg x, inv_pos.mpr hc]⟩ U)

