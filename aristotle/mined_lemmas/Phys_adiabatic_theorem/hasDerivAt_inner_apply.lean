/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped InnerProductSpace

namespace Phys

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Setup

Throughout, `H s` is a time–dependent (self-adjoint) Hamiltonian, `Ev s` a real eigenvalue,
and `P s` the orthogonal projection onto the corresponding eigenspace.  `P₁`, `P₂` are the
first and second derivatives of `P`, `H'` the derivative of `H` and `Ev'` the derivative of `Ev`.
-/

section Defs

variable (H H' P P₁ : ℝ → (E →L[ℂ] E)) (Ev Ev' : ℝ → ℝ)

/-- The shifted Hamiltonian `H s - Ev s` with the eigenprojection added, so that it becomes
invertible exactly when `Ev s` is an isolated (gapped) eigenvalue. -/

lemma hasDerivAt_inner_apply (hHsa : ∀ s, IsSelfAdjoint (H s)) {T : ℝ} {ψ : ℝ → E}
    (hψ : ∀ s, HasDerivAt ψ ((-(Complex.I * (T : ℂ))) • (H s) (ψ s)) s)
    {A A' : ℝ → (E →L[ℂ] E)} {s : ℝ} (hA : HasDerivAt A (A' s) s) :
    HasDerivAt (fun t => ⟪ψ t, A t (ψ t)⟫_ℂ)
      (⟪ψ s, A' s (ψ s)⟫_ℂ +
        (Complex.I * (T : ℂ)) * ⟪ψ s, (H s * A s - A s * H s) (ψ s)⟫_ℂ) s := by
  have hAr : HasDerivAt (fun t => (A t).restrictScalars ℝ) ((A' s).restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt s hA
  have h := (hψ s).inner ℂ (hAr.clm_apply (hψ s))
  convert h using 1
  have hst : ContinuousLinearMap.adjoint (H s) = H s := by
    have h2 := (hHsa s).star_eq
    rwa [ContinuousLinearMap.star_eq_adjoint] at h2
  have hsa : ⟪(H s) (ψ s), A s (ψ s)⟫_ℂ = ⟪ψ s, (H s) (A s (ψ s))⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right (H s) (ψ s) (A s (ψ s)), hst]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, inner_sub_right,
    inner_add_right, inner_smul_right, inner_smul_left, map_smul, hsa,
    map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
    ContinuousLinearMap.coe_restrictScalars']
  ring

/-- Conservation of the norm. -/
