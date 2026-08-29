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

theorem robertson_uncertainty
    (A B : Module.End ℂ E) (hA : IsSymmetricOp A) (hB : IsSymmetricOp B)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    Delta A ψ * Delta B ψ ≥ ‖expect ⁅A, B⁆ ψ‖ / 2 := by
  set f : E := A ψ - expect A ψ • ψ with hf
  set g : E := B ψ - expect B ψ • ψ with hg
  have hid := inner_sub_inner_eq_expect_commutator A B hA hB ψ hψ
  have h1 : ‖expect ⁅A, B⁆ ψ‖ ≤ ‖(inner ℂ f g : ℂ)‖ + ‖(inner ℂ g f : ℂ)‖ := by
    rw [← hid]
    exact norm_sub_le _ _
  -- Cauchy-Schwarz : `norm_inner_le_norm`
  have h2 : ‖(inner ℂ f g : ℂ)‖ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm f g
  have h3 : ‖(inner ℂ g f : ℂ)‖ ≤ ‖g‖ * ‖f‖ := norm_inner_le_norm g f
  have : ‖expect ⁅A, B⁆ ψ‖ ≤ 2 * (‖f‖ * ‖g‖) := by
    have := h1.trans (add_le_add h2 h3)
    linarith [this]
  simp only [Delta, ge_iff_le, ← hf, ← hg]
  linarith

end QC

