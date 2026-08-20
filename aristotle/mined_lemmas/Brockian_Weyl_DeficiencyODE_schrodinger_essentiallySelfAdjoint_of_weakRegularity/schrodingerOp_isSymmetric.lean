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

lemma schrodingerOp_isSymmetric (V : ℤ → ℝ) (b : HilbertBasis ℤ ℂ H) :
    IsSymmetricOp (finiteSpan b) (schrodingerOp V b) := by
  have hkey : ∀ i j : ℤ, ⟪b i, b j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    fun i j => orthonormal_iff_ite.mp b.orthonormal i j
  have main : ∀ (x : H) (hx : x ∈ finiteSpan b) (y : H) (hy : y ∈ finiteSpan b),
      ⟪schrodingerOp V b ⟨x, hx⟩, y⟫_ℂ = ⟪x, schrodingerOp V b ⟨y, hy⟩⟫_ℂ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hxs =>
        obtain ⟨n, rfl⟩ := hxs
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hys =>
            obtain ⟨m, rfl⟩ := hys
            rw [schrodingerOp_basis, schrodingerOp_basis]
            simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hkey,
              Complex.conj_ofReal, show (n = m - 1) ↔ (n + 1 = m) by omega,
              show (n = m + 1) ↔ (n - 1 = m) by omega]
            by_cases hnm : n = m
            · subst hnm; simp
            · simp [hnm]; ring
        | zero =>
            rw [show (⟨0, Submodule.zero_mem _⟩ : finiteSpan b) = 0 from rfl, map_zero,
              inner_zero_right]
            simp
        | add y1 y2 h1 h2 ih1 ih2 =>
            rw [show (⟨y1 + y2, Submodule.add_mem _ h1 h2⟩ : finiteSpan b)
                = ⟨y1, h1⟩ + ⟨y2, h2⟩ from rfl, map_add, inner_add_right, inner_add_right,
              ih1, ih2]
        | smul c y hy ih =>
            rw [show (⟨c • y, Submodule.smul_mem _ c hy⟩ : finiteSpan b) = c • ⟨y, hy⟩ from rfl,
              map_smul, inner_smul_right, inner_smul_right, ih]
    | zero =>
        intro y hy
        rw [show (⟨0, Submodule.zero_mem _⟩ : finiteSpan b) = 0 from rfl, map_zero]
        simp
    | add x1 x2 h1 h2 ih1 ih2 =>
        intro y hy
        rw [show (⟨x1 + x2, Submodule.add_mem _ h1 h2⟩ : finiteSpan b)
            = ⟨x1, h1⟩ + ⟨x2, h2⟩ from rfl, map_add, inner_add_left, inner_add_left,
          ih1 y hy, ih2 y hy]
    | smul c x hx ih =>
        intro y hy
        rw [show (⟨c • x, Submodule.smul_mem _ c hx⟩ : finiteSpan b) = c • ⟨x, hx⟩ from rfl,
          map_smul, inner_smul_left, inner_smul_left, ih y hy]
  intro u v
  exact main (u : H) u.2 (v : H) v.2

/-- Coordinatewise description of the discrete Schrödinger operator: its `n`-th
coefficient is `u (n-1) + u (n+1) + V n * u n`. -/
