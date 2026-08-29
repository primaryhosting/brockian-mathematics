/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

open ContinuousLinearMap

/-- **Ehrenfest theorem.**

Let `psi : ℝ → E` be a state trajectory in a complex inner product space `E`, obeying the
Schrödinger equation `i ℏ ψ'(t) = H ψ(t)` with a (bounded) self-adjoint Hamiltonian `H`, and let
`A : ℝ → (E →L[ℂ] E)` be a (possibly time dependent) observable with time derivative `A'` at `t`.
Writing the expectation value as `⟨A⟩(s) = ⟪ψ(s), A(s) ψ(s)⟫`, we have

`d⟨A⟩/dt = (i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`,

where `[H, A] = H A - A H`. -/

theorem ehrenfest
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (hbar : ℝ) (hbar_ne : hbar ≠ 0)
    (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (t : ℝ) (psi' : E) (A' : E →L[ℂ] E)
    (hpsi : HasDerivAt psi psi' t)
    (hA : HasDerivAt A A' t)
    (hSchrodinger : (Complex.I * (hbar : ℂ)) • psi' = H (psi t)) :
    HasDerivAt (fun s => ⟪psi s, A s (psi s)⟫_ℂ)
      ((Complex.I / (hbar : ℂ)) * ⟪psi t, (H.comp (A t) - (A t).comp H) (psi t)⟫_ℂ
        + ⟪psi t, A' (psi t)⟫_ℂ) t := by
  have hbarC : (hbar : ℂ) ≠ 0 := by
    simpa using hbar_ne
  -- Solve the Schrödinger equation for `ψ'`.
  have hpsi'_eq : psi' = (-(Complex.I / (hbar : ℂ))) • H (psi t) := by
    rw [← hSchrodinger, smul_smul]
    have : (-(Complex.I / (hbar : ℂ))) * (Complex.I * (hbar : ℂ)) = 1 := by
      field_simp
      simp [Complex.I_sq]
    rw [this, one_smul]
  have hB : HasDerivAt (fun s => (A s).restrictScalars ℝ) (A'.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hA
  have hAp : HasDerivAt (fun s => A s (psi s)) (A' (psi t) + A t psi') t := by
    simpa using hB.clm_apply hpsi
  have hd : HasDerivAt (fun s => ⟪psi s, A s (psi s)⟫_ℂ)
      (⟪psi t, A' (psi t) + A t psi'⟫_ℂ + ⟪psi', A t (psi t)⟫_ℂ) t :=
    hpsi.inner ℂ hAp
  convert hd using 1
  rw [inner_add_right, hpsi'_eq, ContinuousLinearMap.map_smul, inner_smul_right, inner_smul_left,
    hH (psi t) (A t (psi t))]
  have hconj : (starRingEnd ℂ) (-(Complex.I / (hbar : ℂ))) = Complex.I / (hbar : ℂ) := by
    simp [map_div₀, Complex.conj_I, Complex.conj_ofReal, neg_div]
  rw [hconj]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right]
  ring

/-- The Ehrenfest theorem, expressed with `deriv`. -/
