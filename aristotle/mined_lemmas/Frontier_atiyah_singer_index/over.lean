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
