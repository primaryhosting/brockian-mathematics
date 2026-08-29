/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped ComplexInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Ehrenfest's theorem.**

Let `psi : ℝ → E` be a state evolving in a complex inner product space according to the
Schrödinger equation `iℏ ψ'(t) = H ψ(t)` (written here as `ψ'(t) = (-i/ℏ) • H ψ(t)`), with
`H` a bounded self-adjoint Hamiltonian, and let `A : ℝ → (E →L[ℂ] E)` be a (possibly
time-dependent) observable with derivative `A'` at `t`.  Then the expectation value
`⟨A⟩(s) = ⟪ψ s, A s (ψ s)⟫` is differentiable at `t` with

`d⟨A⟩/dt = (i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`.
-/
theorem ehrenfest
    (hbar : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, ⟪H x, y⟫ = ⟪x, H y⟫)
    (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (A' : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / (hbar : ℂ)) • H (psi t)) t)
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => ⟪psi s, A s (psi s)⟫)
      ((Complex.I / (hbar : ℂ)) *
          ⟪psi t, ((H.comp (A t) - (A t).comp H) : E →L[ℂ] E) (psi t)⟫
        + ⟪psi t, A' (psi t)⟫) t := by
  have hB : HasDerivAt (fun s => (A s).restrictScalars ℝ) (A'.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hA
  have hnum : HasDerivAt (fun s => A s (psi s))
      (A' (psi t) + (A t) ((-Complex.I / (hbar : ℂ)) • H (psi t))) t :=
    hB.clm_apply hpsi
  have key := HasDerivAt.inner (𝕜 := ℂ) hpsi hnum
  convert key using 1
  have h1 : ⟪psi t, (A t) ((-Complex.I / (hbar : ℂ)) • H (psi t))⟫
      = (-Complex.I / (hbar : ℂ)) * ⟪psi t, (A t) (H (psi t))⟫ := by
    rw [ContinuousLinearMap.map_smul, inner_smul_right]
  have h2 : ⟪(-Complex.I / (hbar : ℂ)) • H (psi t), (A t) (psi t)⟫
      = (Complex.I / (hbar : ℂ)) * ⟪psi t, H ((A t) (psi t))⟫ := by
    rw [inner_smul_left, hH]
    congr 1
    simp [map_div₀, Complex.conj_ofReal, neg_div]
  have h3 : ⟪psi t, ((H.comp (A t) - (A t).comp H) : E →L[ℂ] E) (psi t)⟫
      = ⟪psi t, H ((A t) (psi t))⟫ - ⟪psi t, (A t) (H (psi t))⟫ := by
    simp
  rw [inner_add_right, h1, h2, h3]
  ring

/-- Ehrenfest's theorem, stated for `deriv`. -/
theorem ehrenfest_deriv
    (hbar : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, ⟪H x, y⟫ = ⟪x, H y⟫)
    (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (A' : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / (hbar : ℂ)) • H (psi t)) t)
    (hA : HasDerivAt A A' t) :
    deriv (fun s => ⟪psi s, A s (psi s)⟫) t =
      (Complex.I / (hbar : ℂ)) *
          ⟪psi t, ((H.comp (A t) - (A t).comp H) : E →L[ℂ] E) (psi t)⟫
        + ⟪psi t, A' (psi t)⟫ :=
  (ehrenfest hbar H hH psi A A' t hpsi hA).deriv

/-- A concrete instance showing that the hypotheses of `ehrenfest` are satisfiable and that the
conclusion is non-vacuous: on `E = ℂ` with a free Hamiltonian `H = 0`, a stationary state `z`,
and the explicitly time-dependent observable `A s = s • id`, the expectation value is
`s * ‖z‖ ^ 2` and its time derivative is `‖z‖ ^ 2`. -/
example (hbar : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ⟪z, ((s : ℂ) • ContinuousLinearMap.id ℂ ℂ) z⟫)
      ((Complex.I / (hbar : ℂ)) *
          ⟪z, (((0 : ℂ →L[ℂ] ℂ).comp ((t : ℂ) • ContinuousLinearMap.id ℂ ℂ)
              - (((t : ℂ) • ContinuousLinearMap.id ℂ ℂ)).comp (0 : ℂ →L[ℂ] ℂ))
              : ℂ →L[ℂ] ℂ) z⟫
        + ⟪z, (ContinuousLinearMap.id ℂ ℂ) z⟫) t := by
  refine ehrenfest hbar 0 (by simp) (fun _ => z)
    (fun s => (s : ℂ) • ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ) t ?_ ?_
  · simpa using (hasDerivAt_const t z)
  · simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).smul_const
      (ContinuousLinearMap.id ℂ ℂ)

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

