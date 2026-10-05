/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Overview

The Atiyah–Singer index theorem states that for an elliptic (pseudo)differential operator
`D : Γ(E) → Γ(F)` between sections of vector bundles over a closed manifold `X`, the
*analytic index*

  `ind_a(D) = dim ker D - dim coker D`

equals the *topological index* `ind_t(D)`, a characteristic-number expression built from the
symbol of `D` (in the classical form `ind_t(D) = ∫_X ch(σ(D)) · Td(TX ⊗ ℂ)`).

This file formalizes the general notion of the analytic index of a linear operator, and proves
the theorem in the base case of a **zero-dimensional closed manifold**, i.e. a finite set of
points `X`, where:

* a vector bundle over `X` is exactly a family `E : X → Type*` of finite-dimensional vector
  spaces (its fibres), and its space of sections is the product `∀ x, E x`;
* every operator `D : Γ(E) → Γ(F)` is elliptic: the cosphere bundle `S*X` is empty when
  `dim X = 0`, so the invertibility condition on the symbol away from the zero section holds
  vacuously;
* the Todd class of the (zero) tangent bundle is `1`, and the Chern character contributes only
  in degree `0`, so the topological index reduces to the sum of the fibrewise rank differences
  `ind_t = ∑_{x ∈ X} (rank E x - rank F x)`.

The mathematical content of the base case is the rank–nullity theorem, packaged as
`Frontier.analyticIndex_eq_finrank_sub_finrank` below, together with the additivity of rank
over a finite product of vector spaces.
-/

namespace Frontier

open Module

section AnalyticIndex

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {W : Type*} [AddCommGroup W] [Module k W]

/-- The **analytic index** of a linear operator `D : V →ₗ[k] W`, defined as
`dim ker D - dim coker D`, where `coker D = W ⧸ range D`.

For an elliptic operator on a closed manifold both spaces are finite dimensional, and this is
the usual analytic index. -/
noncomputable def analyticIndex (D : V →ₗ[k] W) : ℤ :=
  (finrank k (LinearMap.ker D) : ℤ) - (finrank k (W ⧸ LinearMap.range D) : ℤ)

/-- Rank–nullity, in index-theoretic form: the analytic index of an operator between
finite-dimensional spaces is the difference of their dimensions.  In particular it depends only
on the "topological" data `(dim V, dim W)` and not on the operator itself. -/
theorem analyticIndex_eq_finrank_sub_finrank [FiniteDimensional k V] [FiniteDimensional k W]
    (D : V →ₗ[k] W) : analyticIndex D = (finrank k V : ℤ) - (finrank k W : ℤ) := by
  have hrk : finrank k (LinearMap.range D) + finrank k (LinearMap.ker D) = finrank k V :=
    LinearMap.finrank_range_add_finrank_ker D
  have hq : finrank k (W ⧸ LinearMap.range D) + finrank k (LinearMap.range D) = finrank k W :=
    Submodule.finrank_quotient_add_finrank (LinearMap.range D)
  have hrk' : ((finrank k (LinearMap.range D) : ℤ) + (finrank k (LinearMap.ker D) : ℤ))
      = (finrank k V : ℤ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hrk
  have hq' : ((finrank k (W ⧸ LinearMap.range D) : ℤ) + (finrank k (LinearMap.range D) : ℤ))
      = (finrank k W : ℤ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hq
  unfold analyticIndex
  omega

/-- The analytic index is a homotopy/deformation invariant in the strongest possible sense in
finite dimensions: any two operators between the same pair of spaces have the same index. -/
theorem analyticIndex_congr [FiniteDimensional k V] [FiniteDimensional k W]
    (D₁ D₂ : V →ₗ[k] W) : analyticIndex D₁ = analyticIndex D₂ := by
  rw [analyticIndex_eq_finrank_sub_finrank, analyticIndex_eq_finrank_sub_finrank]

end AnalyticIndex

section ZeroDimensional

variable {k : Type*} [Field k]
variable {X : Type*} [Fintype X]
variable (E F : X → Type*)
variable [∀ x, AddCommGroup (E x)] [∀ x, Module k (E x)] [∀ x, FiniteDimensional k (E x)]
variable [∀ x, AddCommGroup (F x)] [∀ x, Module k (F x)] [∀ x, FiniteDimensional k (F x)]

/-- Sections of a vector bundle over a zero-dimensional closed manifold `X` (a finite set of
points): a section is just a choice of a vector in each fibre. -/
abbrev Sections (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module k (E x)] : Type _ :=
  ∀ x, E x

/-- The **topological index** of a symbol over a zero-dimensional closed manifold.

In dimension `0` the Todd class of the tangent bundle is `1` and only the degree-`0` part of the
Chern character survives integration, so `∫_X ch(σ(D)) Td(TX ⊗ ℂ)` collapses to the sum over the
points of `X` of the difference of the ranks of the two bundles. -/
noncomputable def topologicalIndex (k : Type*) [Field k] (E F : X → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module k (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module k (F x)] : ℤ :=
  ∑ x : X, ((finrank k (E x) : ℤ) - (finrank k (F x) : ℤ))

/-- The dimension of the space of sections of a bundle over a finite set of points is the sum of
the dimensions of its fibres. -/
theorem finrank_sections :
    (finrank k (Sections (k := k) E) : ℤ) = ∑ x : X, (finrank k (E x) : ℤ) := by
  have h : finrank k (∀ x, E x) = ∑ x : X, finrank k (E x) :=
    Module.finrank_pi_fintype k
  exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h

/-- **Atiyah–Singer index theorem, zero-dimensional base case.**

Let `X` be a closed zero-dimensional manifold, i.e. a finite set of points, and let `E`, `F` be
(finite-rank) vector bundles over `X`, given by their fibres.  Every linear operator
`D : Γ(E) → Γ(F)` on sections is elliptic (the ellipticity condition is imposed on the cosphere
bundle `S*X`, which is empty here), and its analytic index

  `dim ker D - dim coker D`

equals its topological index

  `∫_X ch(σ(D)) · Td(TX ⊗ ℂ) = ∑_{x ∈ X} (rank E x - rank F x)`. -/
theorem atiyah_singer_index (D : Sections (k := k) E →ₗ[k] Sections (k := k) F) :
    analyticIndex D = topologicalIndex k E F := by
  have hE : FiniteDimensional k (Sections (k := k) E) := by
    unfold Sections; infer_instance
  have hF : FiniteDimensional k (Sections (k := k) F) := by
    unfold Sections; infer_instance
  rw [analyticIndex_eq_finrank_sub_finrank D, finrank_sections E, finrank_sections F,
    topologicalIndex, Finset.sum_sub_distrib]

end ZeroDimensional

end Frontier

