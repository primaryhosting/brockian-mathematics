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

theorem heisenberg_uncertainty_general
    (X P : H →ₗ[ℂ] H) (hX : X.IsSymmetric) (hP : P.IsSymmetric)
    (ψ : H) (hψ : ‖ψ‖ = 1) (hbar : ℝ) (hbar_nonneg : 0 ≤ hbar)
    (hcomm : X (P ψ) - P (X ψ) = (Complex.I * (hbar : ℂ)) • ψ)
    (a b : ℝ) :
    ‖X ψ - (a : ℂ) • ψ‖ * ‖P ψ - (b : ℂ) • ψ‖ ≥ hbar / 2 := by
  set f : H := X ψ - (a : ℂ) • ψ with hf
  set g : H := P ψ - (b : ℂ) • ψ with hg
  have hnorm : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have key : ⟪f, g⟫_ℂ - ⟪g, f⟫_ℂ = Complex.I * (hbar : ℂ) := by
    rw [hf, hg, inner_shift_sub_conj X P hX hP ψ a b, hcomm, inner_smul_right, hnorm, mul_one]
  have hconj : ⟪g, f⟫_ℂ = (starRingEnd ℂ) ⟪f, g⟫_ℂ := (inner_conj_symm g f).symm
  have h2 : (⟪f, g⟫_ℂ).im - (⟪g, f⟫_ℂ).im = hbar := by
    have h := congrArg Complex.im key
    simpa [Complex.sub_im, Complex.mul_im, Complex.mul_re] using h
  have h3 : (⟪g, f⟫_ℂ).im = -(⟪f, g⟫_ℂ).im := by
    rw [hconj, Complex.conj_im]
  have him : (⟪f, g⟫_ℂ).im = hbar / 2 := by rw [h3] at h2; linarith
  have hle : |(⟪f, g⟫_ℂ).im| ≤ ‖⟪f, g⟫_ℂ‖ := Complex.abs_im_le_norm _
  have hcs : ‖⟪f, g⟫_ℂ‖ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm (𝕜 := ℂ) f g
  rw [him] at hle
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ hbar / 2)] at hle
  linarith

/-- **Heisenberg uncertainty principle.**  If `X` and `P` are symmetric (observable) operators on
a complex inner product space satisfying the canonical commutation relation
`[X, P] ψ = i ℏ ψ` on a normalized state `ψ`, then the product of the uncertainties of `X` and
`P` in the state `ψ` is at least `ℏ / 2`. -/
