/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟪ψ, A ψ⟫` of a (symmetric) operator `A` in the state `ψ`.
For symmetric `A` this complex number is real, so we take its real part. -/

theorem heisenberg_uncertainty
    (X P : H →ₗ[ℂ] H) (hX : X.IsSymmetric) (hP : P.IsSymmetric)
    (ψ : H) (hψ : ‖ψ‖ = 1) (hbar : ℝ) (hbar_nonneg : 0 ≤ hbar)
    (hcomm : X (P ψ) - P (X ψ) = (Complex.I * (hbar : ℂ)) • ψ) :
    uncertainty X ψ * uncertainty P ψ ≥ hbar / 2 :=
  heisenberg_uncertainty_general X P hX hP ψ hψ hbar hbar_nonneg hcomm _ _

end QPhys

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

