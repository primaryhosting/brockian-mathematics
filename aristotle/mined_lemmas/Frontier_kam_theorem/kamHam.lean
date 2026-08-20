import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/

noncomputable def kamHam (ω : Fin n → ℝ) (K : Finset (Fin n → ℤ)) (a b : (Fin n → ℤ) → ℝ)
    (ε : ℝ) (θ I : Fin n → ℝ) : ℝ :=
  (∑ i, ω i * I i) + ε * trigPoly K a b θ

/-- The curve `t ↦ (θ t, I t)` solves Hamilton's equations
`θ̇ = ∂H/∂I`, `İ = -∂H/∂θ` for the Hamiltonian `H`. -/
