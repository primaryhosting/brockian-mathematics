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

theorem finrank_coker_add_finrank_range [FiniteDimensional K W] (T : V →ₗ[K] W) :
    finrank K (W ⧸ LinearMap.range T) + finrank K (LinearMap.range T) = finrank K W :=
  Submodule.finrank_quotient_add_finrank (LinearMap.range T)

/-- **Atiyah–Singer index theorem, base case (a zero-dimensional manifold, i.e. a point).**

For an elliptic operator over a point — that is, an arbitrary linear map `T : V → W`
between finite-dimensional vector spaces — the analytic index `dim ker T - dim coker T`
equals the topological index `dim V - dim W`. -/
