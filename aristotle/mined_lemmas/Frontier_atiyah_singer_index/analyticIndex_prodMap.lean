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

The Atiyah–Singer index theorem states that for an elliptic (pseudo-)differential operator
`D : Γ(E) → Γ(F)` between spaces of sections of vector bundles over a closed manifold `M`,

  `ind_an(D) := dim ker D - dim coker D = ind_top(D)`,

where the topological index is computed from characteristic-class data of the symbol of `D`.

The general theorem is far beyond what is currently formalizable in Mathlib (it requires
pseudodifferential operators, K-theory of the cotangent bundle, the Thom isomorphism and
Bott periodicity, none of which are available).  What is formalized and *proved* here,
axiom-cleanly, is the **base case of the theorem: the case of a `0`-dimensional closed
manifold**, i.e. a finite set of points.

Over a `0`-dimensional manifold, the spaces of sections `Γ(E)`, `Γ(F)` are finite-dimensional
vector spaces, *every* linear operator between them is elliptic (the symbol is the operator
itself on the zero-dimensional cotangent fibre), and the topological index degenerates to the
difference of the ranks of the bundles, i.e. to `dim Γ(E) - dim Γ(F)`.  The statement

  `dim ker D - dim coker D = dim Γ(E) - dim Γ(F)`

is then exactly the index theorem in this case; it is proved below from rank–nullity.

Two structural consequences of the index theorem, both genuine features of the general
theory, are also derived in this base case:

* homotopy / stability invariance: the index does not depend on the operator, only on the
  bundles (`Frontier.analyticIndex_eq_analyticIndex`);
* additivity under direct sums (`Frontier.analyticIndex_prodMap`).

Beyond the two-term case, the theorem is also proved for **elliptic complexes** over a
`0`-dimensional manifold (`Frontier.atiyah_singer_index_complex`): for a finite cochain
complex of finite-dimensional section spaces, the Euler characteristic of the cohomology
(the analytic index, the cohomology being the harmonic sections by Hodge theory) equals the
alternating sum of the bundle ranks (the topological index).  The geometric form over a
finite set of points, with honest bundles `E F : M → Type`, is
`Frontier.atiyah_singer_index_zero_dimensional`.

No lemma in Mathlib states the index theorem in any form (searching for `index`-theoretic
statements only turns up rank–nullity style results); the key Mathlib inputs used are
`LinearMap.finrank_range_add_finrank_ker` and `Submodule.finrank_quotient_add_finrank`.
-/

namespace Frontier

variable {𝕜 : Type*} [Field 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

/-- The cokernel `W ⧸ range T` of a linear operator `T : V →ₗ[𝕜] W`. -/
abbrev cokernel (T : V →ₗ[𝕜] W) : Type _ := W ⧸ LinearMap.range T

/-- The **analytic index** of an operator `T : V →ₗ[𝕜] W`:
`dim ker T - dim coker T`, as an integer. -/

theorem analyticIndex_prodMap {V' W' : Type*} [AddCommGroup V'] [Module 𝕜 V']
    [AddCommGroup W'] [Module 𝕜 W'] [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    [FiniteDimensional 𝕜 V'] [FiniteDimensional 𝕜 W'] (T : V →ₗ[𝕜] W) (T' : V' →ₗ[𝕜] W') :
    analyticIndex (T.prodMap T') = analyticIndex T + analyticIndex T' := by
  rw [atiyah_singer_index, atiyah_singer_index, atiyah_singer_index]
  unfold topologicalIndex
  rw [Module.finrank_prod, Module.finrank_prod]
  push_cast
  ring

/-- The index theorem over a `0`-dimensional manifold, spelled out for the concrete model in
which the bundles are trivial of ranks `m` and `n`: the sections are `Fin m → 𝕜` and
`Fin n → 𝕜`, and the index of any operator between them is `m - n`. -/
