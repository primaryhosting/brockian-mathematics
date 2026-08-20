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
