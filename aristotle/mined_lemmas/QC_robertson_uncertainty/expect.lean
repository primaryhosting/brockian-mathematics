/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟨A⟩_ψ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

noncomputable def expect (A : Module.End ℂ E) (ψ : E) : ℂ := inner ℂ ψ (A ψ)

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of an operator `A`
in the state `ψ`. -/
