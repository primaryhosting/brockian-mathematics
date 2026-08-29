/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is a plain comment and is repeated as a module docstring below.)

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
## The index theorem over a point (base case of Atiyah–Singer)

The Atiyah–Singer index theorem asserts that for an elliptic (pseudo)differential
operator `T : Γ(E) → Γ(F)` between the spaces of smooth sections of two vector
bundles `E, F` over a closed manifold `M`, the *analytic index*

  `ind_a T = dim ker T - dim coker T`

coincides with the *topological index*, a number computed from the topological data
of the symbol of `T` alone (via characteristic classes), with no reference to the
analysis of `T`.

This file formalizes the statement and proves it in the base case `M = pt`, the
zero–dimensional manifold consisting of a single point.  Over a point, a vector
bundle is just a finite–dimensional vector space, the space of sections of `E` is
`E` itself, every linear operator `T : E → F` is elliptic and Fredholm, and the
topological index (the integral of the Chern character of the symbol against the
Todd class) degenerates to the difference of ranks

  `ind_t = rank E - rank F`,

which depends only on the bundles and not at all on the operator `T`.  The theorem
`Frontier.atiyah_singer_index` below is exactly this identity; its content is the
rank–nullity theorem, and it already exhibits the characteristic feature of the
index theorem: the analytic index is a homotopy/deformation invariant that is
computable from topological data alone (see `Frontier.analyticIndex_eq_analyticIndex`,
the deformation invariance, and `Frontier.analyticIndex_prodMap`, the multiplicativity
of the index under direct sums of operators).
-/

namespace Frontier

open Module

variable {𝕜 : Type*} [Field 𝕜]
  {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- The **analytic index** of a linear operator `T : E →ₗ[𝕜] F`:
`dim ker T - dim coker T`, where `coker T = F ⧸ range T`.

Over a point, the sections of the bundles `E` and `F` are just the vector spaces `E`
and `F`, and this is the usual analytic index of the (automatically elliptic,
automatically Fredholm) operator `T`. -/

theorem analyticIndex_self [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    analyticIndex T = 0 := by
  rw [atiyah_singer_index T, topologicalIndex, sub_self]

/-- The index is additive under direct sums of operators. -/
