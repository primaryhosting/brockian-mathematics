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

lemma adjointGraph_isClosed (G : OperatorGraph H) :
    IsClosed ((adjointGraph G : OperatorGraph H) : Set (H × H)) := by
  have hset : ((adjointGraph G : OperatorGraph H) : Set (H × H))
      = ⋂ q ∈ (G : Set (H × H)), {p : H × H | ⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ} := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro q hq
      exact hp q hq
    · intro hp q hq
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hp
      exact hp q hq
  rw [hset]
  refine isClosed_iInter fun q => isClosed_iInter fun _ => isClosed_eq ?_ ?_
  · exact continuous_const.inner continuous_fst
  · exact continuous_const.inner continuous_snd

