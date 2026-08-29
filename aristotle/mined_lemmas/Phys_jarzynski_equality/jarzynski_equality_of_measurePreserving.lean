/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- The canonical partition function `Z = ∑ₓ e^{-βH(x)}` of a Hamiltonian `H`
on a finite phase space at inverse temperature `β`. -/

theorem jarzynski_equality_of_measurePreserving (μ : Measure Ω) (β : ℝ) (hβ : β ≠ 0)
    (H₀ H₁ : Ω → ℝ) (φ : Ω ≃ᵐ Ω) (hφ : MeasurePreserving φ μ μ)
    (hZ₀ : 0 < partitionFunctionOn μ β H₀) (hZ₁ : 0 < partitionFunctionOn μ β H₁) :
    ∫ x, gibbsDensity μ β H₀ x * Real.exp (-β * (H₁ (φ x) - H₀ x)) ∂μ
      = Real.exp (-β * (freeEnergyOn μ β H₁ - freeEnergyOn μ β H₀)) := by
  have hpt : ∀ x, gibbsDensity μ β H₀ x * Real.exp (-β * (H₁ (φ x) - H₀ x))
      = Real.exp (-β * H₁ (φ x)) / partitionFunctionOn μ β H₀ := by
    intro x
    rw [gibbsDensity, div_mul_eq_mul_div, ← Real.exp_add]
    ring_nf
  calc ∫ x, gibbsDensity μ β H₀ x * Real.exp (-β * (H₁ (φ x) - H₀ x)) ∂μ
      = ∫ x, Real.exp (-β * H₁ (φ x)) / partitionFunctionOn μ β H₀ ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x, Real.exp (-β * H₁ (φ x)) ∂μ) / partitionFunctionOn μ β H₀ := by
        rw [integral_div]
    _ = partitionFunctionOn μ β H₁ / partitionFunctionOn μ β H₀ := by
        rw [hφ.integral_comp' (fun y => Real.exp (-β * H₁ y))]
        rfl
    _ = Real.exp (-β * (freeEnergyOn μ β H₁ - freeEnergyOn μ β H₀)) := by
        rw [freeEnergyOn, freeEnergyOn]
        have h : -β * (-(Real.log (partitionFunctionOn μ β H₁)) / β
            - -(Real.log (partitionFunctionOn μ β H₀)) / β)
            = Real.log (partitionFunctionOn μ β H₁)
              - Real.log (partitionFunctionOn μ β H₀) := by
          field_simp
          ring
        rw [h, Real.exp_sub, Real.exp_log hZ₁, Real.exp_log hZ₀]

end Continuous

end Phys

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

