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

namespace Frontier

open Real MeasureTheory intervalIntegral

/-- The BCS pairing integral
`∫₀^ω dξ / √(ξ² + Δ²)`, i.e. the right-hand side of the BCS gap equation for a
constant density of states, energy cutoff `ω` and gap parameter `Δ`. -/

theorem bcs_gap_binding_unique {g omega : ℝ} (hg : 0 < g) (hw : 0 < omega) :
    ∃! Delta : ℝ, 0 < Delta ∧ g * bcsGapIntegral omega Delta = 1 := by
  have hs : 0 < Real.sinh (1 / g) := Mathlib.Meta.Positivity.sinh_pos_of_pos (by positivity)
  refine ⟨omega / Real.sinh (1 / g), ⟨by positivity, ?_⟩, ?_⟩
  · have hdiv : omega / (omega / Real.sinh (1 / g)) = Real.sinh (1 / g) := by field_simp
    rw [bcsGapIntegral_eq_arsinh (by positivity), hdiv, Real.arsinh_sinh]
    field_simp
  · rintro D ⟨hD, hDeq⟩
    rw [bcsGapIntegral_eq_arsinh hD] at hDeq
    have h1 : Real.arsinh (omega / D) = 1 / g := by
      field_simp at hDeq ⊢; linarith [hDeq]
    have h2 : omega / D = Real.sinh (1 / g) := by
      rw [← h1, Real.sinh_arsinh]
    field_simp at h2 ⊢
    linarith [h2]

end Frontier

