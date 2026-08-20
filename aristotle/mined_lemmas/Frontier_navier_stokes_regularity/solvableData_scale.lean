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

theorem solvableData_scale {ν : ℝ} {u₀ : E3 → E3} (h : SolvableData ν u₀) {c : ℝ} (hc : 0 < c) :
    SolvableData ν (fun x => c • u₀ (c • x)) := by
  obtain ⟨u, p, hsol, hinit, C, hC⟩ := h
  refine ⟨fun t x => c • u (c ^ 2 * t) (c • x), fun t x => c ^ 2 * p (c ^ 2 * t) (c • x),
    isNSSolution_scale hsol c, fun x => by simp [hinit], ⟨c ^ 2 * ((c ^ 3)⁻¹ * C), ?_⟩⟩
  intro t ht
  rw [integral_norm_sq_scale (u (c ^ 2 * t)) hc]
  have hle : (∫ y : E3, ‖u (c ^ 2 * t) y‖ ^ 2) ≤ C := hC _ (by positivity)
  have hpos : (0 : ℝ) < (c ^ 3)⁻¹ := inv_pos.mpr (pow_pos hc 3)
  have := mul_le_mul_of_nonneg_left hle hpos.le
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ## Reduction to small initial energy -/

/-- The Navier–Stokes rescaling `U ↦ c U(c ·)` of a Schwartz field, as a Schwartz field. -/
