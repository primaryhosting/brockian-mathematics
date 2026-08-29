/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

set_option grind.warning false

namespace Frontier

/-- A real Möbius transformation `x ↦ (a x + b) / (c x + d)`.  These are exactly the
boundary values on `ℝ = ∂ℍ` of the conformal automorphisms of the upper half-plane. -/

theorem crossing_limit_eq_of_modulus_eq
    (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ) (C : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hconv : ∀ x₁ x₂ x₃ x₄ : ℝ, Distinct4 x₁ x₂ x₃ x₄ →
      Filter.Tendsto (fun n => P n x₁ x₂ x₃ x₄) Filter.atTop (nhds (C x₁ x₂ x₃ x₄)))
    (hC : ConformallyInvariant C)
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ}
    (hx : Distinct4 x₁ x₂ x₃ x₄) (hy : Distinct4 y₁ y₂ y₃ y₄)
    (hmod : modulus x₁ x₂ x₃ x₄ = modulus y₁ y₂ y₃ y₄) :
    Filter.Tendsto (fun n => P n x₁ x₂ x₃ x₄) Filter.atTop (nhds (C y₁ y₂ y₃ y₄)) := by
  have := hconv x₁ x₂ x₃ x₄ hx
  rwa [eq_of_modulus_eq hC hx hy hmod] at this

end Frontier

