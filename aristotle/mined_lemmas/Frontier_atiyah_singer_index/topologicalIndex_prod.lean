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
