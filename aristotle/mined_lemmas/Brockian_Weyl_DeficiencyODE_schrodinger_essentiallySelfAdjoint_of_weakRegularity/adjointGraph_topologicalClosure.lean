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

lemma adjointGraph_topologicalClosure (G : OperatorGraph H) :
    adjointGraph G.topologicalClosure = adjointGraph G := by
  refine le_antisymm (adjointGraph_antitone (Submodule.le_topologicalClosure G)) ?_
  intro p hp
  have hclosed : IsClosed {q : H × H | ⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hsub : (G : Set (H × H)) ⊆ {q : H × H | ⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ} := fun q hq => hp q hq
  intro q hq
  have hmem : q ∈ closure (G : Set (H × H)) := by
    simpa [Submodule.topologicalClosure_coe] using hq
  exact hclosed.closure_subset_iff.mpr hsub hmem

/-- A graph is self-adjoint when it agrees with the graph of its adjoint. -/
