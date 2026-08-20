import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

/-- The Berry curvature `F = ∂_{k₁} A₂ - ∂_{k₂} A₁` of a `U(1)` Berry connection
`(A₁, A₂)` on the Brillouin torus, written in coordinates. -/

lemma chernNumber_landau (n : ℤ) : chernNumber (landauA₁ n) (landauA₂ n) = (n : ℝ) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hinner : ∀ k₁ : ℝ,
      (∫ k₂ in (0:ℝ)..(2 * Real.pi), berryCurvature (landauA₁ n) (landauA₂ n) k₁ k₂)
        = (n : ℝ) := by
    intro k₁
    simp only [berryCurvature_landau]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  simp only [chernNumber, hinner]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- **TKNN.** For the Landau-gauge band with Berry connection `(landauA₁ n, landauA₂ n)`,
the Hall conductance equals the Chern number times `e² / h`, and that Chern number is the
integer `n`; hence the Hall conductance is quantized in units of `e² / h`. -/
