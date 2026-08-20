import Mathlib
/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Real intervalIntegral

/-- The BCS kernel `x ↦ 1 / √(x² + Δ²)` is continuous when `Δ ≠ 0`. -/

theorem bcs_gap_binding (lam ω : ℝ) (hlam : 0 < lam) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ = ω / Real.sinh (1 / lam) ∧
      lam * (∫ x in (0:ℝ)..ω, 1 / Real.sqrt (x ^ 2 + Δ ^ 2)) = 1 := by
  have hs : 0 < Real.sinh (1 / lam) := by
    positivity
  refine ⟨ω / Real.sinh (1 / lam), by positivity, rfl, ?_⟩
  rw [integral_bcs_kernel (by positivity) ω]
  have : ω / (ω / Real.sinh (1 / lam)) = Real.sinh (1 / lam) := by
    field_simp
  rw [this, Real.arsinh_sinh]
  field_simp

end Frontier

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

