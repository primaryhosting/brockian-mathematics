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

open scoped InnerProductSpace
open scoped NNReal

namespace Brockian.Weyl.DeficiencyODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An (in general unbounded) linear operator on a Hilbert space `H` is encoded by its graph,
a linear subspace of `H × H`. -/
abbrev OperatorGraph (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Submodule ℂ (H × H)

/-- The graph of the adjoint of the operator with graph `G`:
`(u, v)` belongs to it iff `⟪T x, u⟫ = ⟪x, v⟫` for all `(x, T x) ∈ G`. -/

lemma isSymmetricGraph_topologicalClosure {G : OperatorGraph H} (h : IsSymmetricGraph G) :
    IsSymmetricGraph G.topologicalClosure := by
  have h1 : G.topologicalClosure ≤ adjointGraph G := closure_le_adjointGraph h
  have h2 : G ≤ adjointGraph G.topologicalClosure := by
    intro p hp q hq
    exact (adjoint_rel_symm p q).mpr (h1 hq p hp)
  exact Submodule.topologicalClosure_minimal G h2 (adjointGraph_isClosed _)

/-! ### The basic norm identity for symmetric operators -/

/-- The **basic identity** `‖T x + c x‖² = ‖T x‖² + |c|² ‖x‖²` valid for a symmetric operator `T`
and a purely imaginary number `c`. -/
