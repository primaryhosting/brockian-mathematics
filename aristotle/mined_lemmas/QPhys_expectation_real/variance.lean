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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expectation values of a symmetric operator are real. -/

noncomputable def variance (A : H →ₗ[ℂ] H) (psi : H) : ℝ :=
  (⟪psi, A (A psi)⟫_ℂ).re - ((⟪psi, A psi⟫_ℂ).re) ^ 2

/-- For a symmetric operator and a normalized state, the variance `⟨A²⟩ - ⟨A⟩²`
equals the squared norm of the centered vector `A ψ - ⟨A⟩ ψ`. -/
