import Mathlib

/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
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


theorem bcs_gap_binding (g ω : ℝ) (hg : 0 < g) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ g * ∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2) = 1 := by
  have hsinh : 0 < Real.sinh (1 / g) := Real.sinh_pos_iff.mpr (by positivity)
  refine ⟨ω / Real.sinh (1 / g), by positivity, ?_⟩
  rw [bcs_integral _ _ (by positivity)]
  have hdiv : ω / (ω / Real.sinh (1 / g)) = Real.sinh (1 / g) := by
    field_simp
  rw [hdiv, Real.arsinh_sinh]
  field_simp

end Frontier

