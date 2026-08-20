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

theorem bcsGapIntegral_eq_arsinh (ω Δ : ℝ) (hΔ : 0 < Δ) :
    bcsGapIntegral ω Δ = Real.arsinh (ω / Δ) := by
  have hcont : Continuous fun ξ : ℝ => (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ := by
    apply Continuous.inv₀
    · fun_prop
    · intro x
      have : 0 < x ^ 2 + Δ ^ 2 := by positivity
      positivity
  have hderiv : ∀ ξ ∈ Set.uIcc (0 : ℝ) ω,
      HasDerivAt (fun t : ℝ => Real.arsinh (t / Δ)) (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ ξ := by
    intro ξ _
    have h1 : HasDerivAt (fun t : ℝ => t / Δ) (1 / Δ) ξ := by
      simpa using (hasDerivAt_id ξ).div_const Δ
    have h2 := (Real.hasDerivAt_arsinh (ξ / Δ)).comp ξ h1
    convert h2 using 1
    have he : 1 + (ξ / Δ) ^ 2 = (ξ ^ 2 + Δ ^ 2) / Δ ^ 2 := by field_simp; ring
    have hs : Real.sqrt (1 + (ξ / Δ) ^ 2) = Real.sqrt (ξ ^ 2 + Δ ^ 2) / Δ := by
      rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hΔ.le]
    rw [hs]
    have hpos : 0 < Real.sqrt (ξ ^ 2 + Δ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  rw [bcsGapIntegral,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 ω)]
  simp

/-- **Cooper pairing / BCS gap binding.**  For every attractive coupling `g > 0` and every
Debye cut-off `ω > 0`, the BCS gap equation `g * ∫_0^ω dξ / sqrt(ξ² + Δ²) = 1` has a
solution with a strictly positive (in particular nonzero) gap `Δ`. -/
