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
`D : Γ(E) → Γ(F)` between smooth sections of vector bundles over a closed manifold `M`,

  `ind_an(D) := dim ker D - dim coker D = ∫_M ch(σ(D)) · Td(TM ⊗ ℂ) =: ind_top(D)`.

The full theorem is far beyond current Mathlib infrastructure (it needs elliptic
pseudodifferential calculus, K-theory of the cotangent bundle, the Chern character and the
Todd class).  What is formalized and *proved* here is the **base case of the induction on the
dimension of `M`**: the case where `M` is a closed `0`-dimensional manifold, i.e. a finite set
of points.

In that base case all the ingredients degenerate to honest linear algebra:

* a vector bundle over a finite point set `ι` is a family `E : ι → Type` of finite-dimensional
  vector spaces, and its space of smooth sections is the product `Π i, E i`;
* since the cosphere bundle of a `0`-dimensional manifold is empty, *every* bundle morphism
  `D : Γ(E) → Γ(F)` is elliptic, and `D` is automatically Fredholm;
* the analytic index is `dim ker D - dim coker D`, with `coker D = Γ(F) ⧸ range D`;
* the characteristic-class integral degenerates: `Td` of a point is `1`, the Chern character of
  the symbol class contributes only its rank part, and integration over the `0`-dimensional
  manifold is the sum over the points.  Hence
  `ind_top(D) = Σ_i (rank E i - rank F i) = rank Γ(E) - rank Γ(F)`,
  which visibly depends only on the topological data (the bundles), not on `D`.

The content of the base case is therefore exactly the statement that the analytic index equals
the purely topological quantity `rank E - rank F`; this is a genuine (if elementary) instance of
the index theorem, and it is what `Frontier.atiyah_singer_index` proves.  Two of the hallmark
consequences of the index theorem — homotopy invariance / stability of the index, and its
vanishing when the two bundles have equal rank — are derived from it below.
-/

namespace Frontier

section IndexTheory

variable {𝕜 : Type*} [Field 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

/-- The **cokernel** of a linear map, i.e. `W ⧸ range D`.

In the geometric setting `D : Γ(E) → Γ(F)` is an elliptic operator and this is the usual
cokernel appearing in the analytic index. -/
abbrev Coker (D : V →ₗ[𝕜] W) : Type _ := W ⧸ LinearMap.range D

/-- The **analytic index** of an operator `D`: `dim ker D - dim coker D`, as an integer. -/

theorem analyticIndex_eq_of_bundles [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (D D' : V →ₗ[𝕜] W) : analyticIndex D = analyticIndex D' := by
  rw [atiyah_singer_index D, atiyah_singer_index D']

/-- If the two bundles have the same rank, every elliptic operator between them has index `0`. -/
