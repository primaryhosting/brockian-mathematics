/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Momentum selection rule.**  If `T` preserves the inner product (a translation
operator is unitary) and two states are `T`-eigenvectors with *different* eigenvalues,
the first one being a unit vector, then the two states are orthogonal.

This is the step of the Lieb–Schultz–Mattis argument which guarantees that the twisted
state, carrying a different lattice momentum, is orthogonal to the ground state. -/

theorem lieb_schultz_mattis_of_twist_commutation
    {H T U : E →ₗ[ℂ] E} {ψ₀ : E} {E₀ ε : ℝ} {t : ℂ} {twoS : ℕ}
    (hspin : Odd twoS)
    (hT : ∀ x y : E, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hψnorm : ‖ψ₀‖ = 1)
    (hmin : ∀ φ : E, ‖φ‖ = 1 → E₀ ≤ (⟪φ, H φ⟫_ℂ).re)
    (hground : (⟪ψ₀, H ψ₀⟫_ℂ).re = E₀)
    (hTψ : T ψ₀ = t • ψ₀)
    (hUnorm : ‖U ψ₀‖ = 1)
    (hcomm : T (U ψ₀) = ((-1 : ℂ)) ^ twoS • U (T ψ₀))
    (hEnergy : (⟪U ψ₀, H (U ψ₀)⟫_ℂ).re ≤ E₀ + ε) :
    (∃ φ : E, ‖φ‖ = 1 ∧ ⟪ψ₀, φ⟫_ℂ = 0 ∧
      (⟪φ, H φ⟫_ℂ).re = (⟪ψ₀, H ψ₀⟫_ℂ).re) ∨
    (∃ φ : E, ‖φ‖ = 1 ∧ ⟪ψ₀, φ⟫_ℂ = 0 ∧
      (⟪ψ₀, H ψ₀⟫_ℂ).re < (⟪φ, H φ⟫_ℂ).re ∧
      (⟪φ, H φ⟫_ℂ).re ≤ (⟪ψ₀, H ψ₀⟫_ℂ).re + ε) := by
  have hTU : T (U ψ₀) = ((-1 : ℂ) ^ twoS * t) • (U ψ₀) := by
    rw [hcomm, hTψ, map_smul, smul_smul]
  exact lieb_schultz_mattis hspin hT hψnorm hmin hground hTψ hUnorm hTU hEnergy

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

