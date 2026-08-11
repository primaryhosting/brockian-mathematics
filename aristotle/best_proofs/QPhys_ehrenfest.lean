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

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Differentiability of a (possibly time-dependent) bounded operator, transported along
`restrictScalars ℝ`. -/
lemma hasDerivAt_restrictScalars {A : ℝ → (E →L[ℂ] E)} {A' : E →L[ℂ] E} {t : ℝ}
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => (A s).restrictScalars ℝ) (A'.restrictScalars ℝ) t := by
  have hL : HasFDerivAt (fun B : E →L[ℂ] E => B.restrictScalars ℝ)
      (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ) (A t) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt
  simpa using hL.comp_hasDerivAt t hA

/-- The time derivative of `s ↦ (A s) (ψ s)` for a differentiable operator-valued function `A`
and a differentiable vector-valued function `ψ`. -/
lemma hasDerivAt_apply {A : ℝ → (E →L[ℂ] E)} {A' : E →L[ℂ] E} {psi : ℝ → E} {psi' : E} {t : ℝ}
    (hA : HasDerivAt A A' t) (hpsi : HasDerivAt psi psi' t) :
    HasDerivAt (fun s => (A s) (psi s)) (A' (psi t) + (A t) psi') t :=
  (hasDerivAt_restrictScalars hA).clm_apply hpsi

/-- **Ehrenfest's theorem.**

For a state `ψ : ℝ → E` in a complex inner product space evolving according to the
Schrödinger equation `i ℏ ψ'(t) = H ψ(t)` with a bounded self-adjoint Hamiltonian `H`,
and a (possibly time-dependent) bounded observable `A`, the expectation value
`⟨A⟩(t) = ⟪ψ t, A t (ψ t)⟫` satisfies

`d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
theorem ehrenfest
    {ℏ : ℝ} (hℏ : ℏ ≠ 0)
    (Hop : E →L[ℂ] E) (hH : ∀ x y : E, ⟪Hop x, y⟫_ℂ = ⟪x, Hop y⟫_ℂ)
    (psi : ℝ → E) (psi' : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (A' : ℝ → (E →L[ℂ] E)) (t : ℝ)
    (hpsi : HasDerivAt psi (psi' t) t)
    (hA : HasDerivAt A (A' t) t)
    (hSch : (Complex.I * (ℏ : ℂ)) • psi' t = Hop (psi t)) :
    HasDerivAt (fun s => ⟪psi s, (A s) (psi s)⟫_ℂ)
      ((Complex.I / (ℏ : ℂ)) * ⟪psi t, (⁅Hop, A t⁆ : E →L[ℂ] E) (psi t)⟫_ℂ
        + ⟪psi t, (A' t) (psi t)⟫_ℂ) t := by
  have hℏC : (ℏ : ℂ) ≠ 0 := by exact_mod_cast hℏ
  -- the Schrödinger equation, solved for `ψ'`
  have hpsi'val : psi' t = (-Complex.I / (ℏ : ℂ)) • Hop (psi t) := by
    rw [← hSch, smul_smul]
    have : (-Complex.I / (ℏ : ℂ)) * (Complex.I * (ℏ : ℂ)) = 1 := by
      field_simp
      rw [Complex.I_sq]
      ring
    rw [this, one_smul]
  have hderiv := (hpsi.inner ℂ (hasDerivAt_apply hA hpsi))
  refine hderiv.congr_deriv ?_
  rw [inner_add_right, hpsi'val]
  rw [map_smul, inner_smul_right, inner_smul_left]
  have hHA : ⟪Hop (psi t), (A t) (psi t)⟫_ℂ = ⟪psi t, Hop ((A t) (psi t))⟫_ℂ := hH _ _
  rw [hHA]
  have hcomm : (⁅Hop, A t⁆ : E →L[ℂ] E) (psi t)
      = Hop ((A t) (psi t)) - (A t) (Hop (psi t)) := by
    simp [Ring.lie_def]
  rw [hcomm, inner_sub_right]
  have hconj : (starRingEnd ℂ) (-Complex.I / (ℏ : ℂ)) = Complex.I / (ℏ : ℂ) := by
    simp [div_eq_mul_inv, Complex.conj_I]
  rw [hconj]
  ring

end QPhys

