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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real ComplexConjugate InnerProductSpace
open Complex MeasureTheory Submodule AddCircle Module

namespace Brockian.Weyl.DeficiencyODE

/-! ## Abstract setting: symmetric operators, deficiency vectors, essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

/-- A densely defined operator `T` with domain `D` is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/

lemma diagOp_isSymmetric (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) :
    IsSymmetric (diagOp b lam) := by
  have key : ∀ (i : ι) (y : span ℂ (Set.range (b : ι → H))),
      ⟪diagOp b lam (spanBasis b i), (y : H)⟫_ℂ = ⟪b i, diagOp b lam y⟫_ℂ := by
    intro i y
    induction y using spanBasis_induction with
    | mem j =>
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [b.orthonormal.2 hij]
    | zero => simp
    | add x y hx hy =>
        simp only [Submodule.coe_add, map_add, inner_add_right] at *
        rw [hx, hy]
    | smul c x hx =>
        simp only [Submodule.coe_smul, map_smul, inner_smul_right] at *
        rw [hx]
  intro x y
  induction x using spanBasis_induction with
  | mem i => simpa using key i y
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
      simp only [Submodule.coe_add, map_add, inner_add_left] at *
      rw [h₁, h₂]
  | smul c x hx =>
      simp only [Submodule.coe_smul, map_smul, inner_smul_left] at *
      rw [hx]

/-- A symmetric diagonal operator whose eigenvectors form a Hilbert basis of the whole space and
whose eigenvalues are real is essentially self-adjoint: the deficiency equation
`(lam i - conj z) * ⟪b i, u⟫ = 0` with `z = ±i` forces all Fourier coefficients of `u` to vanish. -/
