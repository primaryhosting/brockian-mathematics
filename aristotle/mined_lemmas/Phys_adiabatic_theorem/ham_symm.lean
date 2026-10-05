import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Complex MeasureTheory intervalIntegral
open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Phases -/

/-- The unimodular phase `u ↦ exp (i r u)`. -/

theorem ham_symm [CompleteSpace E] (P : ℝ → E →L[ℂ] E) (e₁ e₂ : ℝ) (s : ℝ)
    (hsa : IsSelfAdjoint (P s)) (v w : E) :
    ⟪ham P e₁ e₂ s v, w⟫_ℂ = ⟪v, ham P e₁ e₂ s w⟫_ℂ := by
  have key : ⟪(P s) v, w⟫_ℂ = ⟪v, (P s) w⟫_ℂ :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) v w
  simp only [ham, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, Complex.conj_ofReal, key]

/-- Conservation of the norm along the Schrödinger flow. -/
