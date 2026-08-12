/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Statement: dE_n/dλ = ⟨ψ_n|∂H/∂λ|ψ_n⟩ (Hellmann–Feynman).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Statement: dE_n/dλ = ⟨ψ_n|∂H/∂λ|ψ_n⟩ (Hellmann–Feynman).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (E →L[ℂ] E)` be a family of operators on a complex inner product space,
depending on a parameter `λ`, differentiable at `l` with derivative `dH = ∂H/∂λ`.
Let `psi : ℝ → E` be a differentiable family of normalized eigenvectors,
`H t (ψ t) = En t • ψ t` with real eigenvalues `En t`, and suppose `H l` is symmetric
(self-adjoint) at the point `l`.

Then the energy `En` is differentiable at `l` with
`dEn/dλ = ⟨ψ, (∂H/∂λ) ψ⟩`. -/
theorem hellmann_feynman (H : ℝ → (E →L[ℂ] E)) (dH : E →L[ℂ] E) (psi : ℝ → E) (dpsi : E)
    (En : ℝ → ℝ) (l : ℝ)
    (hH : HasDerivAt H dH l) (hpsi : HasDerivAt psi dpsi l)
    (hsym : ∀ x y : E, ⟪H l x, y⟫_ℂ = ⟪x, H l y⟫_ℂ)
    (heig : ∀ t, H t (psi t) = (En t : ℂ) • psi t)
    (hnorm : ∀ t, ‖psi t‖ = 1) :
    HasDerivAt En (⟪psi l, dH (psi l)⟫_ℂ).re l := by
  -- Derivative of `t ↦ H t (ψ t)` by the product (bilinear application) rule.
  have hHpsi : HasDerivAt (fun t => H t (psi t)) (dH (psi l) + H l dpsi) l := by
    have h1 : HasDerivAt (fun t => (H t).restrictScalars ℝ) (dH.restrictScalars ℝ) l :=
      (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt l hH
    simpa using h1.clm_apply hpsi
  -- Differentiating the normalization `⟪ψ, ψ⟫ = 1`.
  have hzero : ⟪psi l, dpsi⟫_ℂ + ⟪dpsi, psi l⟫_ℂ = 0 := by
    have h2 : HasDerivAt (fun t => ⟪psi t, psi t⟫_ℂ) (⟪psi l, dpsi⟫_ℂ + ⟪dpsi, psi l⟫_ℂ) l :=
      hpsi.inner ℂ hpsi
    have h3 : (fun t => ⟪psi t, psi t⟫_ℂ) = fun _ : ℝ => (1 : ℂ) := by
      funext t
      rw [inner_self_eq_norm_sq_to_K, hnorm t]
      norm_num
    rw [h3] at h2
    exact h2.unique (hasDerivAt_const _ _)
  -- Differentiating the energy expectation value `⟪ψ, H ψ⟫`.
  have hF : HasDerivAt (fun t => ⟪psi t, H t (psi t)⟫_ℂ)
      (⟪psi l, dH (psi l) + H l dpsi⟫_ℂ + ⟪dpsi, H l (psi l)⟫_ℂ) l := hpsi.inner ℂ hHpsi
  have hval : (fun t => ⟪psi t, H t (psi t)⟫_ℂ) = fun t => ((En t : ℝ) : ℂ) := by
    funext t
    rw [heig t, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm t]
    norm_num
  -- The terms involving `dψ` cancel, by symmetry of `H l` and the normalization.
  have hsimp : ⟪psi l, dH (psi l) + H l dpsi⟫_ℂ + ⟪dpsi, H l (psi l)⟫_ℂ
      = ⟪psi l, dH (psi l)⟫_ℂ := by
    have e1 : ⟪psi l, H l dpsi⟫_ℂ = (En l : ℂ) * ⟪psi l, dpsi⟫_ℂ := by
      rw [← hsym, heig l, inner_smul_left]
      simp
    have e2 : ⟪dpsi, H l (psi l)⟫_ℂ = (En l : ℂ) * ⟪dpsi, psi l⟫_ℂ := by
      rw [heig l, inner_smul_right]
    rw [inner_add_right, e1, e2]
    have hc : (En l : ℂ) * ⟪psi l, dpsi⟫_ℂ + (En l : ℂ) * ⟪dpsi, psi l⟫_ℂ = 0 := by
      rw [← mul_add, hzero, mul_zero]
    linear_combination hc
  rw [hval, hsimp] at hF
  simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt l hF

/-- Hellmann–Feynman theorem, complex-valued form: if in addition `∂H/∂λ` is symmetric,
then the derivative of the energy is literally the (real) expectation value
`⟨ψ | ∂H/∂λ | ψ⟩`. -/
theorem hellmann_feynman_eq (H : ℝ → (E →L[ℂ] E)) (dH : E →L[ℂ] E) (psi : ℝ → E) (dpsi : E)
    (En : ℝ → ℝ) (dEn : ℝ) (l : ℝ)
    (hH : HasDerivAt H dH l) (hpsi : HasDerivAt psi dpsi l) (hEn : HasDerivAt En dEn l)
    (hsym : ∀ x y : E, ⟪H l x, y⟫_ℂ = ⟪x, H l y⟫_ℂ)
    (hsymd : ∀ x y : E, ⟪dH x, y⟫_ℂ = ⟪x, dH y⟫_ℂ)
    (heig : ∀ t, H t (psi t) = (En t : ℂ) • psi t)
    (hnorm : ∀ t, ‖psi t‖ = 1) :
    (dEn : ℂ) = ⟪psi l, dH (psi l)⟫_ℂ := by
  have hd := hellmann_feynman H dH psi dpsi En l hH hpsi hsym heig hnorm
  have hre : dEn = (⟪psi l, dH (psi l)⟫_ℂ).re := hEn.unique hd
  have hconj : (starRingEnd ℂ) ⟪psi l, dH (psi l)⟫_ℂ = ⟪psi l, dH (psi l)⟫_ℂ := by
    rw [inner_conj_symm, hsymd]
  have him : (⟪psi l, dH (psi l)⟫_ℂ).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  rw [hre]
  exact Complex.ext rfl (by simpa using him.symm)

end Phys

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

