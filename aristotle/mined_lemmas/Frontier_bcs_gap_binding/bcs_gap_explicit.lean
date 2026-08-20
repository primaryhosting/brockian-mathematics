import Mathlib

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

/-!
# BCS gap equation: existence of a nonzero gap for any attractive coupling

At zero temperature, in the standard BCS model with a constant density of states and a
Debye cut-off `ω > 0`, the gap equation reads

  `1 = g * ∫_0^ω dξ / sqrt(ξ² + Δ²)`,

where `g > 0` is the (attractive) dimensionless coupling `N(0)·V`.  The integral is
computed in closed form as `arsinh (ω / Δ)`, and the equation therefore always has the
strictly positive solution `Δ = ω / sinh (1 / g)` — the Cooper instability: *any*
attractive coupling, no matter how weak, binds a nonzero gap.
-/

namespace Frontier

/-- The BCS gap functional: `∫_0^ω dξ / sqrt(ξ² + Δ²)` (constant density of states,
zero temperature, Debye cut-off `ω`). -/

theorem bcs_gap_explicit (g ω : ℝ) (hg : 0 < g) (hω : 0 < ω) :
    g * bcsGapIntegral ω (ω / Real.sinh (1 / g)) = 1 := by
  have hs : 0 < Real.sinh (1 / g) := Mathlib.Meta.Positivity.sinh_pos_of_pos (by positivity)
  have hΔ : 0 < ω / Real.sinh (1 / g) := by positivity
  rw [bcsGapIntegral_eq_arsinh _ _ hΔ]
  have hquot : ω / (ω / Real.sinh (1 / g)) = Real.sinh (1 / g) := by field_simp
  rw [hquot, Real.arsinh_sinh]
  field_simp

/-- Uniqueness of the positive BCS gap: for `g, ω > 0`, a positive gap `Δ` solves the gap
equation if and only if it equals `ω / sinh (1 / g)`. -/
