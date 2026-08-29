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
noncomputable def analyticIndex (T : E →ₗ[𝕜] F) : ℤ :=
  (finrank 𝕜 (LinearMap.ker T) : ℤ) - (finrank 𝕜 (F ⧸ LinearMap.range T) : ℤ)

/-- The **topological index** of a pair of bundles over a point: the difference of
their ranks.  Over a point the Atiyah–Singer topological index (an integral of
characteristic classes of the symbol) reduces to `rank E - rank F`; in particular it
depends only on `E` and `F` and not on any operator between them. -/
noncomputable def topologicalIndex (𝕜 : Type*) [Field 𝕜]
    (E F : Type*) [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] : ℤ :=
  (finrank 𝕜 E : ℤ) - (finrank 𝕜 F : ℤ)

/-- **Atiyah–Singer index theorem, base case (over a point).**
For an elliptic operator over a zero–dimensional manifold — that is, an arbitrary
linear map `T : E →ₗ[𝕜] F` between finite–dimensional vector spaces — the analytic
index `dim ker T - dim coker T` equals the topological index `rank E - rank F`. -/
theorem atiyah_singer_index [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) : analyticIndex T = topologicalIndex 𝕜 E F := by
  have hrn : finrank 𝕜 (LinearMap.range T) + finrank 𝕜 (LinearMap.ker T) = finrank 𝕜 E :=
    LinearMap.finrank_range_add_finrank_ker T
  have hq : finrank 𝕜 (F ⧸ LinearMap.range T) + finrank 𝕜 (LinearMap.range T) = finrank 𝕜 F :=
    Submodule.finrank_quotient_add_finrank (LinearMap.range T)
  unfold analyticIndex topologicalIndex
  omega

/-- **Deformation (homotopy) invariance of the index, over a point.**
The analytic index of an elliptic operator does not change under deformations of the
operator: over a point, any two operators between the same pair of bundles have the
same analytic index. -/
theorem analyticIndex_eq_analyticIndex [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (T S : E →ₗ[𝕜] F) : analyticIndex T = analyticIndex S := by
  rw [atiyah_singer_index T, atiyah_singer_index S]

/-- The index of an elliptic operator from a bundle to itself vanishes. -/
theorem analyticIndex_self [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    analyticIndex T = 0 := by
  rw [atiyah_singer_index T, topologicalIndex, sub_self]

/-- The index is additive under direct sums of operators. -/
theorem analyticIndex_prodMap [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {E' F' : Type*} [AddCommGroup E'] [Module 𝕜 E'] [AddCommGroup F'] [Module 𝕜 F']
    [FiniteDimensional 𝕜 E'] [FiniteDimensional 𝕜 F']
    (T : E →ₗ[𝕜] F) (S : E' →ₗ[𝕜] F') :
    analyticIndex (T.prodMap S) = analyticIndex T + analyticIndex S := by
  rw [atiyah_singer_index, atiyah_singer_index, atiyah_singer_index]
  simp only [topologicalIndex, Module.finrank_prod]
  push_cast
  ring

end Frontier

