import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A symmetric (formally self-adjoint) linear operator has real expectation values. -/

theorem heisenberg_uncertainty (X P : E →ₗ[ℂ] E) (ψ : E) (hbar : ℝ)
    (hψ : ‖ψ‖ = 1)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : E, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hcomm : X (P ψ) - P (X ψ) = (Complex.I * hbar) • ψ) :
    |hbar| / 2 ≤ ‖X ψ - ⟪ψ, X ψ⟫_ℂ • ψ‖ * ‖P ψ - ⟪ψ, P ψ⟫_ℂ • ψ‖ := by
  set a : ℂ := ⟪ψ, X ψ⟫_ℂ with ha
  set b : ℂ := ⟪ψ, P ψ⟫_ℂ with hb
  set u : E := X ψ - a • ψ with hu
  set v : E := P ψ - b • ψ with hv
  have hnorm : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hac : (starRingEnd ℂ) a = a := expectation_real X hX ψ
  have hbc : (starRingEnd ℂ) b = b := expectation_real P hP ψ
  -- compute ⟪u, v⟫
  have h1 : ⟪u, v⟫_ℂ = ⟪X ψ, P ψ⟫_ℂ - a * b := by
    simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hac,
      hnorm]
    have e1 : ⟪X ψ, ψ⟫_ℂ = a := by rw [ha, hX]
    have e2 : ⟪ψ, P ψ⟫_ℂ = b := hb.symm
    rw [e1, e2]
    ring
  have h2 : ⟪v, u⟫_ℂ = ⟪P ψ, X ψ⟫_ℂ - b * a := by
    simp only [hu, hv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hbc, hnorm]
    have e1 : ⟪P ψ, ψ⟫_ℂ = b := by rw [hb, hP]
    have e2 : ⟪ψ, X ψ⟫_ℂ = a := ha.symm
    rw [e1, e2]
    ring
  have hcommute : ⟪X ψ, P ψ⟫_ℂ - ⟪P ψ, X ψ⟫_ℂ = Complex.I * hbar := by
    rw [hX ψ (P ψ), hP ψ (X ψ), ← inner_sub_right, hcomm, inner_smul_right, hnorm, mul_one]
  have h3 : ⟪u, v⟫_ℂ - (starRingEnd ℂ) ⟪u, v⟫_ℂ = Complex.I * hbar := by
    rw [inner_conj_symm, h1, h2]
    linear_combination hcommute
  have h4 : (⟪u, v⟫_ℂ).im = hbar / 2 := by
    have h6 := congrArg Complex.im h3
    simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_neg_eq_add, one_mul, mul_zero,
      zero_add] at h6
    linarith
  have h5 := abs_im_inner_le u v
  rw [h4, abs_div] at h5
  simpa using h5

/-- The usual physicist's form `Δx · Δp ≥ ℏ / 2` for a nonnegative Planck constant `ℏ`. -/
