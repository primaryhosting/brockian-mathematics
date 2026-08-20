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

theorem tknn_chern_hall (e hP : ℝ) (n : ℤ) :
    hallConductance e hP (landauA₁ n) (landauA₂ n)
        = chernNumber (landauA₁ n) (landauA₂ n) * (e ^ 2 / hP) ∧
      chernNumber (landauA₁ n) (landauA₂ n) = (n : ℝ) ∧
      hallConductance e hP (landauA₁ n) (landauA₂ n) = (n : ℝ) * (e ^ 2 / hP) := by
  have hC : chernNumber (landauA₁ n) (landauA₂ n) = (n : ℝ) := chernNumber_landau n
  have hEq : hallConductance e hP (landauA₁ n) (landauA₂ n)
      = chernNumber (landauA₁ n) (landauA₂ n) * (e ^ 2 / hP) := by
    simp only [hallConductance, chernNumber]
    ring
  exact ⟨hEq, hC, by rw [hEq, hC]⟩

end Frontier

