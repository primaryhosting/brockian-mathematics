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

theorem bcs_gap_unique (g ω Δ : ℝ) (hg : 0 < g) (hω : 0 < ω) (hΔ : 0 < Δ) :
    g * bcsGapIntegral ω Δ = 1 ↔ Δ = ω / Real.sinh (1 / g) := by
  have hs : 0 < Real.sinh (1 / g) := Mathlib.Meta.Positivity.sinh_pos_of_pos (by positivity)
  rw [bcsGapIntegral_eq_arsinh _ _ hΔ]
  constructor
  · intro h
    have harc : Real.arsinh (ω / Δ) = 1 / g := by
      field_simp at h ⊢
      linarith [h]
    have : ω / Δ = Real.sinh (1 / g) := by
      have := congrArg Real.sinh harc
      rwa [Real.sinh_arsinh] at this
    field_simp at this ⊢
    linarith [this]
  · intro h
    subst h
    have hquot : ω / (ω / Real.sinh (1 / g)) = Real.sinh (1 / g) := by field_simp
    rw [hquot, Real.arsinh_sinh]
    field_simp

end Frontier

#print axioms Frontier.bcs_gap_unique
#print axioms Frontier.bcs_gap_binding
#print axioms Frontier.bcs_gap_explicit

