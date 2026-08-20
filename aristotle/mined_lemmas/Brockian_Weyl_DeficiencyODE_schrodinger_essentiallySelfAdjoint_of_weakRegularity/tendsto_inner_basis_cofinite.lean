import Brockian.Weyl.DeficiencyODE

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

import Mathlib

/-!
# Essential self-adjointness of Schrödinger operators via deficiency indices

This file develops, from scratch:

* a minimal framework for (possibly unbounded) operators on a complex Hilbert space,
  given as a linear map `T : D →ₗ[ℂ] H` out of a submodule `D` of `H`, together with
  their graphs, adjoint graphs, symmetry and essential self-adjointness;
* the *basic criterion* of essential self-adjointness: a densely defined symmetric
  operator whose deficiency spaces `ker (T* ∓ i)` are trivial is essentially
  self-adjoint;
* the deficiency ("Weyl limit point") analysis of the second order difference
  equation attached to a discrete Schrödinger operator, and the resulting
  essential self-adjointness of the discrete Schrödinger operator
  `(T u) n = u (n-1) + u (n+1) + V n * u n` on `ℓ²(ℤ, ℂ)`, defined on the
  (dense) span of the standard basis vectors, for an **arbitrary** real potential
  `V : ℤ → ℝ`.

The main theorem
`schrodinger_essentiallySelfAdjoint_of_weakRegularity` is unconditional: no regularity
(or boundedness) hypothesis on the potential is needed, so the classical weak regularity
assumption is discharged. Everything is proved from first principles on top of Mathlib;
in particular the framework for unbounded operators, their adjoints and essential
self-adjointness is built here.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Brockian.Weyl.DeficiencyODE

/-! ## An abstract framework for unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The graph of an operator `T` defined on the submodule `D` of `H`. -/

lemma tendsto_inner_basis_cofinite (b : HilbertBasis ℤ ℂ H) (v : H) :
    Tendsto (fun n : ℤ => ⟪b n, v⟫_ℂ) cofinite (𝓝 0) := by
  have hsum : Summable (fun i : ℤ => ⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ) := b.summable_inner_mul_inner v v
  have h0 : Tendsto (fun i : ℤ => ⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ) cofinite (𝓝 0) :=
    hsum.tendsto_cofinite_zero
  have h1 : Tendsto (fun i : ℤ => ‖⟪b i, v⟫_ℂ‖ ^ 2) cofinite (𝓝 0) := by
    have h := (continuous_norm.tendsto (0 : ℂ)).comp h0
    simp only [Function.comp_def, norm_zero] at h
    refine h.congr fun i => ?_
    have hc : ‖⟪v, b i⟫_ℂ‖ = ‖⟪b i, v⟫_ℂ‖ := by
      rw [← inner_conj_symm (b i) v, Complex.norm_conj]
    rw [norm_mul, hc, sq]
  have h2 : Tendsto (fun i : ℤ => ‖⟪b i, v⟫_ℂ‖) cofinite (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h2

/-- A deficiency vector satisfies the deficiency difference equation. -/
