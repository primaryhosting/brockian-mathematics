/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[H, A] = H A - A H` of two continuous linear operators. -/
def commutator (H A : E →L[ℂ] E) : E →L[ℂ] E := H.comp A - A.comp H

/--
**Ehrenfest's theorem.**

Let `psi : ℝ → E` be a state trajectory in a complex inner product space obeying the
Schrödinger equation `iℏ ψ'(t) = H ψ(t)` (written here as `ψ'(t) = (-i/ℏ) • H (ψ t)`),
with `H` a symmetric (bounded) Hamiltonian, and let `A : ℝ → (E →L[ℂ] E)` be a
(possibly time-dependent) observable with derivative `A'` at `t`.

Then the expectation value `⟨A⟩(t) = ⟪ψ t, A t (ψ t)⟫` is differentiable at `t` with

`d⟨A⟩/dt = (i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`.
-/
theorem ehrenfest
    (hbar : ℝ) (H : E →L[ℂ] E) (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (A' : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / hbar) • H (psi t)) t)
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => ⟪psi s, A s (psi s)⟫_ℂ)
      ((Complex.I / hbar) * ⟪psi t, (commutator H (A t)) (psi t)⟫_ℂ
        + ⟪psi t, A' (psi t)⟫_ℂ) t := by
  have hAR : HasDerivAt (fun s => (A s).restrictScalars ℝ) (A'.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hA
  have hmain := hpsi.inner ℂ (hAR.clm_apply hpsi)
  simp only [ContinuousLinearMap.coe_restrictScalars'] at hmain
  convert hmain using 1
  simp only [commutator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, inner_sub_right, inner_add_right, inner_smul_right, inner_smul_left,
    map_smul, map_div₀, Complex.conj_I, map_neg, Complex.conj_ofReal]
  rw [hH (psi t) (A t (psi t))]
  ring

/-- `deriv`-form of Ehrenfest's theorem:
`d⟨A⟩/dt = (i/ℏ)⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`. -/
theorem ehrenfest_deriv
    (hbar : ℝ) (H : E →L[ℂ] E) (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (A' : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / hbar) • H (psi t)) t)
    (hA : HasDerivAt A A' t) :
    deriv (fun s => ⟪psi s, A s (psi s)⟫_ℂ) t
      = (Complex.I / hbar) * ⟪psi t, (commutator H (A t)) (psi t)⟫_ℂ
        + ⟪psi t, A' (psi t)⟫_ℂ :=
  (ehrenfest hbar H hH psi A A' t hpsi hA).deriv

/-- A stationary state: `ψ(t) = e^{-i E₀ t / ℏ} v` for an eigenvector `v` of `H`
with real eigenvalue `E₀`. -/
noncomputable def stationaryState (hbar E0 : ℝ) (v : E) : ℝ → E :=
  fun s => Complex.exp (-Complex.I * E0 * s / hbar) • v

/-- The stationary state solves the Schrödinger equation `ψ'(t) = (-i/ℏ) H ψ(t)`. -/
theorem hasDerivAt_stationaryState (hbar E0 : ℝ) (H : E →L[ℂ] E) (v : E)
    (hv : H v = (E0 : ℂ) • v) (t : ℝ) :
    HasDerivAt (stationaryState hbar E0 v)
      ((-Complex.I / hbar) • H (stationaryState hbar E0 v t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -Complex.I * E0 * s / hbar)
      (-Complex.I * E0 / hbar) t := by
    simpa [mul_div_assoc] using
      ((hasDerivAt_id t).ofReal_comp.const_mul (-Complex.I * E0)).div_const hbar
  have hexp := (hlin.cexp).smul_const v
  refine hexp.congr_deriv ?_
  simp only [stationaryState, hv, smul_smul, ContinuousLinearMap.map_smul]
  congr 1
  field_simp

/-- **Non-vacuity / consistency check.** In a stationary state, the expectation value of a
time-independent observable `B` is constant: its derivative vanishes.  This is derived from
`QPhys.ehrenfest`, so in particular the hypotheses of that theorem are satisfiable. -/
theorem ehrenfest_stationary (hbar E0 : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ) (v : E) (hv : H v = (E0 : ℂ) • v)
    (B : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s => ⟪stationaryState hbar E0 v s, B (stationaryState hbar E0 v s)⟫_ℂ) 0 t := by
  set psi := stationaryState hbar E0 v with hpsidef
  have hpsi := hasDerivAt_stationaryState hbar E0 H v hv t
  have key := ehrenfest hbar H hH psi (fun _ => B) 0 t hpsi (hasDerivAt_const t B)
  refine key.congr_deriv ?_
  have hHpsi : H (psi t) = (E0 : ℂ) • psi t := by
    rw [hpsidef]
    simp only [stationaryState, ContinuousLinearMap.map_smul, hv]
    rw [smul_comm]
  have h1 : ⟪psi t, H (B (psi t))⟫_ℂ = (E0 : ℂ) * ⟪psi t, B (psi t)⟫_ℂ := by
    rw [← hH (psi t) (B (psi t)), hHpsi, inner_smul_left]
    simp
  have h2 : ⟪psi t, B (H (psi t))⟫_ℂ = (E0 : ℂ) * ⟪psi t, B (psi t)⟫_ℂ := by
    rw [hHpsi]
    simp
  simp only [commutator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, inner_sub_right, h1, h2]
  simp

end QPhys

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

