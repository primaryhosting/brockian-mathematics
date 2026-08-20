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
lemma expectation_real (A : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) (psi : H) :
    (starRingEnd ℂ) ⟪psi, A psi⟫_ℂ = ⟪psi, A psi⟫_ℂ := by
  rw [inner_conj_symm, hA]

/-- The commutator expectation: from `[A,B] ψ = i ħ ψ` and `‖ψ‖ = 1`. -/
lemma inner_commutator (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hB : ∀ x y : H, ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (hbar : ℝ) (psi : H) (hpsi : ‖psi‖ = 1)
    (hcomm : A (B psi) - B (A psi) = ((hbar : ℂ) * Complex.I) • psi) :
    ⟪A psi, B psi⟫_ℂ - ⟪B psi, A psi⟫_ℂ = (hbar : ℂ) * Complex.I := by
  have hpp : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  have h := congrArg (fun y : H => ⟪psi, y⟫_ℂ) hcomm
  simp only [inner_sub_right, inner_smul_right, hpp, mul_one] at h
  rw [hA psi (B psi), hB psi (A psi)]
  exact h

/-- **Heisenberg uncertainty principle.**  For symmetric (observable) operators `A`, `B`
on a complex inner product space satisfying the canonical commutation relation
`A (B ψ) - B (A ψ) = i ħ ψ` on a normalized state `ψ`, the product of the standard
deviations is at least `ħ / 2`.  The proof combines the commutator identity with the
Cauchy–Schwarz inequality (`norm_inner_le_norm`). -/
theorem heisenberg_uncertainty (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hB : ∀ x y : H, ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (hbar : ℝ) (psi : H) (hpsi : ‖psi‖ = 1)
    (hcomm : A (B psi) - B (A psi) = ((hbar : ℂ) * Complex.I) • psi) :
    ‖A psi - ⟪psi, A psi⟫_ℂ • psi‖ * ‖B psi - ⟪psi, B psi⟫_ℂ • psi‖ ≥ hbar / 2 := by
  set z : ℂ := ⟪psi, A psi⟫_ℂ with hz
  set w : ℂ := ⟪psi, B psi⟫_ℂ with hw
  set u : H := A psi - z • psi with hu
  set v : H := B psi - w • psi with hv
  have hpp : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hApsi : ⟪A psi, psi⟫_ℂ = z := by rw [hz, hA]
  have hBpsi : ⟪B psi, psi⟫_ℂ = w := by rw [hw, hB]
  -- expand the inner product of the centered vectors
  have huv : ⟪u, v⟫_ℂ = ⟪A psi, B psi⟫_ℂ - z * w := by
    rw [hu, hv]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hpp, mul_one, hApsi, hw, hz]
    ring
  have hvu : ⟪v, u⟫_ℂ = ⟪B psi, A psi⟫_ℂ - w * z := by
    rw [hu, hv]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hpp, mul_one, hBpsi, hw, hz]
    ring
  have hcomm' : ⟪A psi, B psi⟫_ℂ - ⟪B psi, A psi⟫_ℂ = (hbar : ℂ) * Complex.I :=
    inner_commutator A B hA hB hbar psi hpsi hcomm
  have hdiff : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = (hbar : ℂ) * Complex.I := by
    rw [huv, hvu]; rw [← hcomm']; ring
  have hconj : ⟪v, u⟫_ℂ = (starRingEnd ℂ) ⟪u, v⟫_ℂ := (inner_conj_symm v u).symm
  have hnorm : |hbar| ≤ 2 * ‖⟪u, v⟫_ℂ‖ := by
    have h1 : ‖(hbar : ℂ) * Complex.I‖ ≤ ‖⟪u, v⟫_ℂ‖ + ‖⟪v, u⟫_ℂ‖ := by
      rw [← hdiff]
      exact norm_sub_le _ _
    have h2 : ‖⟪v, u⟫_ℂ‖ = ‖⟪u, v⟫_ℂ‖ := by rw [hconj, RCLike.norm_conj]
    have h3 : ‖(hbar : ℂ) * Complex.I‖ = |hbar| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h3, h2] at h1
    linarith
  have hcs : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : hbar ≤ 2 * (‖u‖ * ‖v‖) := le_trans (le_trans (le_abs_self hbar) hnorm) (by linarith)
  linarith

#print axioms QPhys.heisenberg_uncertainty

/-- The variance of the observable `A` in the state `psi`:
`⟨A²⟩ - ⟨A⟩²`, taking real parts (both expectation values are real for symmetric `A`). -/
noncomputable def variance (A : H →ₗ[ℂ] H) (psi : H) : ℝ :=
  (⟪psi, A (A psi)⟫_ℂ).re - ((⟪psi, A psi⟫_ℂ).re) ^ 2

/-- For a symmetric operator and a normalized state, the variance `⟨A²⟩ - ⟨A⟩²`
equals the squared norm of the centered vector `A ψ - ⟨A⟩ ψ`. -/
lemma variance_eq_norm_centered_sq (A : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) (psi : H) (hpsi : ‖psi‖ = 1) :
    variance A psi = ‖A psi - ⟪psi, A psi⟫_ℂ • psi‖ ^ 2 := by
  have hpp : ⟪psi, psi⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hzc : (starRingEnd ℂ) ⟪psi, A psi⟫_ℂ = ⟪psi, A psi⟫_ℂ := expectation_real A hA psi
  have hzim : (⟪psi, A psi⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hzc
  have hApsi : ⟪A psi, psi⟫_ℂ = ⟪psi, A psi⟫_ℂ := hA _ _
  have hAA : ⟪A psi, A psi⟫_ℂ = ⟪psi, A (A psi)⟫_ℂ := hA _ _
  have key : ⟪A psi - ⟪psi, A psi⟫_ℂ • psi, A psi - ⟪psi, A psi⟫_ℂ • psi⟫_ℂ
      = ⟪psi, A (A psi)⟫_ℂ - ⟪psi, A psi⟫_ℂ * ⟪psi, A psi⟫_ℂ := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hpp,
      mul_one, hApsi, hAA, hzc]
    ring
  have h2 := congrArg Complex.re key
  rw [inner_self_eq_norm_sq_to_K] at h2
  norm_cast at h2
  simp only [Complex.sub_re, Complex.mul_re, hzim, mul_zero, sub_zero] at h2
  simp only [variance]
  rw [pow_two]
  exact h2.symm

/-- **Heisenberg uncertainty principle, variance form.**  The product of the standard
deviations `Δ_A = √(⟨A²⟩ - ⟨A⟩²)` and `Δ_B = √(⟨B²⟩ - ⟨B⟩²)` of two symmetric observables
obeying the canonical commutation relation `A (B ψ) - B (A ψ) = i ħ ψ` on a normalized
state `ψ` is at least `ħ / 2`. -/
theorem heisenberg_uncertainty_variance (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hB : ∀ x y : H, ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (hbar : ℝ) (psi : H) (hpsi : ‖psi‖ = 1)
    (hcomm : A (B psi) - B (A psi) = ((hbar : ℂ) * Complex.I) • psi) :
    Real.sqrt (variance A psi) * Real.sqrt (variance B psi) ≥ hbar / 2 := by
  rw [variance_eq_norm_centered_sq A hA psi hpsi, variance_eq_norm_centered_sq B hB psi hpsi,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact heisenberg_uncertainty A B hA hB hbar psi hpsi hcomm

#print axioms QPhys.heisenberg_uncertainty_variance

end QPhys

