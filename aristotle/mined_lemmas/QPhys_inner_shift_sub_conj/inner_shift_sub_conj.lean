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

lemma inner_shift_sub_conj (X P : H →ₗ[ℂ] H) (hX : X.IsSymmetric) (hP : P.IsSymmetric)
    (ψ : H) (a b : ℝ) :
    ⟪X ψ - (a : ℂ) • ψ, P ψ - (b : ℂ) • ψ⟫_ℂ
      - ⟪P ψ - (b : ℂ) • ψ, X ψ - (a : ℂ) • ψ⟫_ℂ
      = ⟪ψ, X (P ψ) - P (X ψ)⟫_ℂ := by
  have hXs : ⟪X ψ, P ψ⟫_ℂ = ⟪ψ, X (P ψ)⟫_ℂ := by
    rw [← hX ψ (P ψ)]
  have hPs : ⟪P ψ, X ψ⟫_ℂ = ⟪ψ, P (X ψ)⟫_ℂ := by
    rw [← hP ψ (X ψ)]
  have hXψ : ⟪X ψ, ψ⟫_ℂ = ⟪ψ, X ψ⟫_ℂ := hX ψ ψ
  have hPψ : ⟪P ψ, ψ⟫_ℂ = ⟪ψ, P ψ⟫_ℂ := hP ψ ψ
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hXs, hPs]
  rw [← hXψ, ← hPψ]
  ring

