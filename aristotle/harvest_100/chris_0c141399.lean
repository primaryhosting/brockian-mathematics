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

/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨A⟩ψ = ⟪ψ, A ψ⟫` of an observable `A` in the state `ψ`. -/
noncomputable def expect (A : H →ₗ[ℂ] H) (psi : H) : ℂ := inner ℂ psi (A psi)

/-- The centered observable `A - ⟨A⟩` applied to `ψ`. -/
noncomputable def centered (A : H →ₗ[ℂ] H) (psi : H) : H := A psi - expect A psi • psi

/-- The standard deviation (uncertainty) `ΔA = ‖(A - ⟨A⟩) ψ‖` of the observable `A`
in the state `ψ`. -/
noncomputable def stdDev (A : H →ₗ[ℂ] H) (psi : H) : ℝ := ‖centered A psi‖

/-- For a symmetric operator the expectation value is real. -/
lemma expect_conj {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (psi : H) :
    conj (expect A psi) = expect A psi := by
  unfold expect
  rw [inner_conj_symm]
  exact hA psi psi

/-- The inner product of two centered observables, in terms of the uncentered ones. -/
lemma inner_centered {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric)
    {psi : H} (hpsi : ‖psi‖ = 1) :
    inner ℂ (centered A psi) (centered B psi)
      = inner ℂ psi (A (B psi)) - expect A psi * expect B psi := by
  have hnorm : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  have hAB : (inner ℂ (A psi) (B psi) : ℂ) = inner ℂ psi (A (B psi)) := hA psi (B psi)
  have hAp : (inner ℂ (A psi) psi : ℂ) = expect A psi := hA psi psi
  simp only [centered, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, hnorm, hAB, hAp, expect_conj hA]
  have hBp : (inner ℂ psi (B psi) : ℂ) = expect B psi := rfl
  rw [hBp]
  ring

/-- The commutator relation transferred to the centered vectors. -/
lemma inner_centered_sub_swap {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {psi : H} (hpsi : ‖psi‖ = 1) {hbar : ℝ}
    (hcomm : A (B psi) - B (A psi) = (Complex.I * hbar) • psi) :
    inner ℂ (centered A psi) (centered B psi) - inner ℂ (centered B psi) (centered A psi)
      = Complex.I * hbar := by
  have hnorm : (inner ℂ psi psi : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]
    norm_num
  have h1 := inner_centered (B := B) hA hpsi
  have h2 := inner_centered (B := A) hB hpsi
  rw [h1, h2]
  have hc : (inner ℂ psi (A (B psi)) : ℂ) - inner ℂ psi (B (A psi)) = Complex.I * hbar := by
    rw [← inner_sub_right, hcomm, inner_smul_right, hnorm, mul_one]
  have : expect A psi * expect B psi = expect B psi * expect A psi := by ring
  rw [this]
  linear_combination hc

/-- **Heisenberg uncertainty principle.**  If `X` and `P` are symmetric (self-adjoint)
operators on a complex inner product space satisfying the canonical commutation relation
`[X, P] ψ = i ℏ ψ` on a normalized state `ψ`, then the product of the uncertainties
`Δx · Δp` is at least `ℏ / 2`. -/
theorem heisenberg_uncertainty {X P : H →ₗ[ℂ] H} (hX : X.IsSymmetric) (hP : P.IsSymmetric)
    {psi : H} (hpsi : ‖psi‖ = 1) {hbar : ℝ}
    (hcomm : X (P psi) - P (X psi) = (Complex.I * hbar) • psi) :
    stdDev X psi * stdDev P psi ≥ hbar / 2 := by
  set u := centered X psi with hu
  set v := centered P psi with hv
  have key : (inner ℂ u v : ℂ) - inner ℂ v u = Complex.I * hbar :=
    inner_centered_sub_swap hX hP hpsi hcomm
  have hconj : (inner ℂ v u : ℂ) = conj (inner ℂ u v) := (inner_conj_symm (𝕜 := ℂ) v u).symm
  have him : 2 * (inner ℂ u v : ℂ).im = hbar := by
    have h3 : (inner ℂ v u : ℂ).im = -(inner ℂ u v : ℂ).im := by rw [hconj, Complex.conj_im]
    have h4 := congrArg Complex.im key
    simp only [Complex.sub_im, h3, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at h4
    linarith
  have habs : hbar / 2 ≤ ‖(inner ℂ u v : ℂ)‖ := by
    have h1 : |(inner ℂ u v : ℂ).im| ≤ ‖(inner ℂ u v : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : (inner ℂ u v : ℂ).im = hbar / 2 := by linarith [him]
    rw [h2] at h1
    calc hbar / 2 ≤ |hbar / 2| := le_abs_self _
      _ ≤ _ := h1
  have hcs : ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  exact le_trans habs hcs

/-- Sharper form of the uncertainty principle: the product of the uncertainties is at least
`|ℏ| / 2`. -/
theorem heisenberg_uncertainty_abs {X P : H →ₗ[ℂ] H} (hX : X.IsSymmetric) (hP : P.IsSymmetric)
    {psi : H} (hpsi : ‖psi‖ = 1) {hbar : ℝ}
    (hcomm : X (P psi) - P (X psi) = (Complex.I * hbar) • psi) :
    stdDev X psi * stdDev P psi ≥ |hbar| / 2 := by
  rcases abs_cases hbar with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; exact heisenberg_uncertainty hX hP hpsi hcomm
  · rw [h]
    have hcomm' : P (X psi) - X (P psi) = (Complex.I * (-hbar : ℝ)) • psi := by
      rw [← neg_sub, hcomm]
      push_cast
      module
    have := heisenberg_uncertainty hP hX hpsi hcomm'
    linarith [this, mul_comm (stdDev X psi) (stdDev P psi)]

end QPhys

