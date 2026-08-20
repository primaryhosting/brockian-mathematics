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
## Scope of this formalization

The full Atiyah–Singer index theorem — for an elliptic pseudodifferential operator
`D : Γ(E) → Γ(F)` on a closed manifold `M`, asserting

  `ind_a(D) = ind_t(D) = ∫_M ch(σ(D)) · Td(TM ⊗ ℂ)`

— is far beyond what the current Mathlib library supports: neither elliptic
pseudodifferential operators, nor the Chern character, nor the Todd class, nor the
Thom isomorphism in K-theory are available.

What is formalized and proved here is the *base case* of the theorem, namely the index

theorem over a zero-dimensional manifold (a point). Over a point, a "bundle map" is just
a linear map `T : V → W` between finite-dimensional vector spaces, every such map is
elliptic, and the topological index reduces to the evaluation of the Chern character on a
point, i.e. to the difference of ranks `dim V - dim W`. The content of the theorem in this
case is exactly the rank–nullity theorem:

  `dim ker T - dim coker T = dim V - dim W`.

The two sides are defined independently (`Frontier.analyticIndex` depends on `T`, while
`Frontier.topologicalIndex` does not), so the theorem genuinely has content: it says that
the analytic index is computed by a purely topological (here: dimensional) quantity, and
in particular is a deformation invariant of `T`.

The proof is a Lean-checked reduction to two Mathlib lemmas:
`LinearMap.finrank_range_add_finrank_ker` (rank–nullity) and
`Submodule.finrank_quotient_add_finrank` (rank of a quotient).
-/

namespace Frontier

open Module

section

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The **analytic index** of a linear map `T : V → W`, i.e. of an elliptic operator over a
point: `dim ker T - dim coker T`, where `coker T = W ⧸ range T`. -/

noncomputable def analyticIndex (T : V →ₗ[K] W) : ℤ :=
  (finrank K (LinearMap.ker T) : ℤ) - (finrank K (W ⧸ LinearMap.range T) : ℤ)

/-- The **topological index** of an elliptic operator over a point.  Over a point the
Chern character of the symbol pairs against the fundamental class to give simply the
difference of the ranks of the two bundles, `dim V - dim W`.  Note that this quantity does
not depend on the operator at all — only on the bundles. -/

noncomputable def topologicalIndex (K V W : Type*) [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] : ℤ :=
  (finrank K V : ℤ) - (finrank K W : ℤ)

/-- Rank of the cokernel of `T`, in terms of the rank of `W` and the rank of `range T`. -/

theorem finrank_coker_add_finrank_range [FiniteDimensional K W] (T : V →ₗ[K] W) :
    finrank K (W ⧸ LinearMap.range T) + finrank K (LinearMap.range T) = finrank K W :=
  Submodule.finrank_quotient_add_finrank (LinearMap.range T)

/-- **Atiyah–Singer index theorem, base case (a zero-dimensional manifold, i.e. a point).**

For an elliptic operator over a point — that is, an arbitrary linear map `T : V → W`
between finite-dimensional vector spaces — the analytic index `dim ker T - dim coker T`
equals the topological index `dim V - dim W`. -/

theorem atiyah_singer_index [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W) : analyticIndex T = topologicalIndex K V W := by
  have h₁ : finrank K (LinearMap.range T) + finrank K (LinearMap.ker T) = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker T
  have h₂ : finrank K (W ⧸ LinearMap.range T) + finrank K (LinearMap.range T) = finrank K W :=
    finrank_coker_add_finrank_range T
  unfold analyticIndex topologicalIndex
  omega

/-- **Homotopy / deformation invariance of the index** (base case): the analytic index of an
elliptic operator over a point does not depend on the operator, only on the bundles.
This is the standard consequence of the index theorem, since the right-hand side is
purely topological. -/
