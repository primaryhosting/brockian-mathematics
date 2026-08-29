/-
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/

theorem stdDev_sq {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {psi : H} (hpsi : ‖psi‖ = 1) :
    (stdDev A psi) ^ 2 = (expect (A ∘L A) psi).re - ((expect A psi).re) ^ 2 := by
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hAs : ⟪A psi, psi⟫_ℂ = expect A psi := by
    rw [inner_isSelfAdjoint_left hA]; rfl
  have hEA : ⟪psi, A psi⟫_ℂ = expect A psi := rfl
  have hca := conj_expect hA psi
  have him : (expect A psi).im = 0 := Complex.conj_eq_iff_im.mp hca
  have hAA : ⟪A psi, A psi⟫_ℂ = expect (A ∘L A) psi := by
    rw [inner_isSelfAdjoint_left hA]; rfl
  set u : H := A psi - (expect A psi) • psi with hu
  have hexp : ⟪u, u⟫_ℂ = expect (A ∘L A) psi - (expect A psi) ^ 2 := by
    rw [hu]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hself, hAs, hEA, hAA, hca]
    ring
  have h2 : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [stdDev, ← hu, ← h2, hexp]
  simp [Complex.sub_re, pow_two, Complex.mul_re, him]

/-- The commutator expectation is the difference of the two inner products of the
centered vectors. -/
