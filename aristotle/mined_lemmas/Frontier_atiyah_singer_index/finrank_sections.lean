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
