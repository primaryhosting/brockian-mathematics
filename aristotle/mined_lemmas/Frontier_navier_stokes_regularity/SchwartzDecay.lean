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

theorem SchwartzDecay.const_mul {f : Vec3 → ℝ} (hf : SchwartzDecay f) (c : ℝ) :
    SchwartzDecay (fun x => c * f x) := by
  obtain ⟨hs, hd⟩ := hf
  refine ⟨contDiff_const.mul hs, fun n K => ?_⟩
  obtain ⟨C, hC⟩ := hd n K
  refine ⟨|c| * C, fun x => ?_⟩
  have hfun : (fun x => c * f x) = c • f := by funext y; simp [Pi.smul_apply]
  rw [hfun, iteratedFDeriv_const_smul_apply (hs.of_le (by exact_mod_cast le_top)).contDiffAt,
    norm_smul]
  simp only [Real.norm_eq_abs]
  calc |c| * ‖iteratedFDeriv ℝ n f x‖ * (1 + ‖x‖) ^ K
      = |c| * (‖iteratedFDeriv ℝ n f x‖ * (1 + ‖x‖) ^ K) := by ring
    _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

/-! ## The viscosity scaling reduction -/

/-- Scaling of the divergence by a constant factor. -/
