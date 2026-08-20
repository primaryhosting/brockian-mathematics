import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

lemma mem_opGraph_iff {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) (p : E × E) :
    p ∈ opGraph T ↔ ∃ x : D, ((x : E), T x) = p := by
  simp [opGraph, LinearMap.mem_range, Prod.ext_iff]

/-- The graph of the adjoint operator `T†`: the set of pairs `(u, v)` with
`⟪T x, u⟫ = ⟪x, v⟫` for all `x` in the domain of `T`. -/
