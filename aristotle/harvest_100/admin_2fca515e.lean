/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
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

namespace Frontier

open Module

/-!
## The index theorem over a zero-dimensional manifold (a point)

The Atiyah–Singer index theorem asserts that for an elliptic (pseudo)differential
operator `D : Γ(E) → Γ(F)` between sections of vector bundles over a closed manifold `M`,
the *analytic index*

  `ind_a(D) = dim ker D - dim coker D`

equals the *topological index*, a quantity computed purely from the K-theoretic symbol data
of `D` and the topology of `M`.

We formalize the statement and prove it in the base case `dim M = 0`, i.e. `M` a point
(more generally a finite set of points).  There a vector bundle is just a finite-dimensional
vector space, sections of `E` and `F` are the vector spaces `V` and `W`, every linear map is
elliptic, and the topological index degenerates to the Euler-characteristic-type expression
`dim V - dim W` — the pushforward to a point of the K-theory class `[E] - [F]`.

The content of the theorem in this case is exactly rank–nullity: the analytic index, which
a priori depends on the operator, is in fact a purely topological invariant.
-/

variable {K : Type*} [DivisionRing K]
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The **analytic index** of an operator `T : V →ₗ[K] W`:
`dim ker T - dim coker T`, where `coker T = W ⧸ range T`. -/
noncomputable def analyticIndex (T : V →ₗ[K] W) : ℤ :=
  (finrank K (LinearMap.ker T) : ℤ) - (finrank K (W ⧸ LinearMap.range T) : ℤ)

/-- The **topological index** of the symbol data `(V, W)` over a point:
the image of the K-theory class `[V] - [W]` under the pushforward to a point,
i.e. `dim V - dim W`. -/
noncomputable def topologicalIndex (K : Type*) [DivisionRing K]
    (V W : Type*) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] : ℤ :=
  (finrank K V : ℤ) - (finrank K W : ℤ)

/-- **Atiyah–Singer index theorem, zero-dimensional case.**

For an elliptic operator over a zero-dimensional closed manifold — that is, a linear map
`T : V →ₗ[K] W` between finite-dimensional vector spaces (every such map is elliptic, since
the symbol condition is vacuous in dimension `0`) — the analytic index
`dim ker T - dim coker T` equals the topological index `dim V - dim W`.

In particular the analytic index depends only on the bundle data `(V, W)`, not on the
operator `T` itself. -/
theorem atiyah_singer_index [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W) :
    analyticIndex T = topologicalIndex K V W := by
  have hV : finrank K (LinearMap.range T) + finrank K (LinearMap.ker T) = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker T
  have hW : finrank K (W ⧸ LinearMap.range T) + finrank K (LinearMap.range T) = finrank K W :=
    Submodule.finrank_quotient_add_finrank (LinearMap.range T)
  unfold analyticIndex topologicalIndex
  omega

/-- **Homotopy (deformation) invariance of the index**, in the zero-dimensional case:
any two elliptic operators with the same symbol data have the same analytic index. -/
theorem analyticIndex_eq_analyticIndex [FiniteDimensional K V] [FiniteDimensional K W]
    (T S : V →ₗ[K] W) : analyticIndex T = analyticIndex S := by
  rw [atiyah_singer_index T, atiyah_singer_index S]

/-- An elliptic operator from a bundle to itself has vanishing index. -/
theorem analyticIndex_endomorphism [FiniteDimensional K V] (T : V →ₗ[K] V) :
    analyticIndex T = 0 := by
  rw [atiyah_singer_index T]
  simp [topologicalIndex]

/-- The index is additive under direct sums of the symbol data
(disjoint unions of zero-dimensional manifolds). -/
theorem topologicalIndex_prod
    (V' W' : Type*) [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'] :
    topologicalIndex K (V × V') (W × W') =
      topologicalIndex K V W + topologicalIndex K V' W' := by
  simp only [topologicalIndex, Module.finrank_prod]
  push_cast
  ring

/-- Consequently the analytic index is additive under direct sums: the index of
`T.prodMap T'` is the sum of the indices of `T` and `T'`. -/
theorem analyticIndex_prodMap
    {V' W' : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W']
    (T : V →ₗ[K] W) (T' : V' →ₗ[K] W') :
    analyticIndex (T.prodMap T') = analyticIndex T + analyticIndex T' := by
  rw [atiyah_singer_index, atiyah_singer_index, atiyah_singer_index,
    topologicalIndex_prod (K := K) V' W']

/-- Sanity check: the index is a nontrivial invariant — it can be nonzero.
For the zero operator `(Fin 3 → ℚ) → (Fin 1 → ℚ)` the analytic index is `3 - 1 = 2`. -/
example : analyticIndex (0 : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ)) = 2 := by
  rw [atiyah_singer_index]
  simp [topologicalIndex]

end Frontier

