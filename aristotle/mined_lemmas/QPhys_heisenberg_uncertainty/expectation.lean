/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
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

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`.
We take the real part; for a symmetric operator `A` the inner product is already real. -/

noncomputable def expectation (A : H →ₗ[ℂ] H) (psi : H) : ℝ := (inner ℂ psi (A psi)).re

/-- The uncertainty (standard deviation) `Δ A = ‖(A - ⟨A⟩) ψ‖` of an observable `A`
in the state `ψ`.  For symmetric `A` and normalized `ψ` this equals
`√(⟨A²⟩ - ⟨A⟩²)`, since `‖(A - ⟨A⟩)ψ‖² = ⟪ψ, (A - ⟨A⟩)² ψ⟫`. -/
