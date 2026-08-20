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

lemma adjointGraph_opGraph {S : H →L[ℂ] H} (hS : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ)
    {D : Submodule ℂ H} (hD : Dense (D : Set H)) :
    adjointGraph (opGraph S D) = opGraph S ⊤ := by
  refine le_antisymm ?_ ?_
  · intro p hp
    refine ⟨Submodule.mem_top, ?_⟩
    have hall : ∀ x : H, ⟪x, S p.1 - p.2⟫_ℂ = 0 := by
      have hclosed : IsClosed {x : H | ⟪x, S p.1 - p.2⟫_ℂ = 0} :=
        isClosed_eq (continuous_id.inner continuous_const) continuous_const
      have hsub : (D : Set H) ⊆ {x : H | ⟪x, S p.1 - p.2⟫_ℂ = 0} := by
        intro x hx
        have h1 : ⟪S x, p.1⟫_ℂ = ⟪x, p.2⟫_ℂ := hp (x, S x) ⟨hx, rfl⟩
        rw [hS x p.1] at h1
        simp only [Set.mem_setOf_eq, inner_sub_right, h1, sub_self]
      intro x
      have huniv := hclosed.closure_subset_iff.mpr hsub
      rw [hD.closure_eq] at huniv
      exact huniv (Set.mem_univ x)
    have h2 : S p.1 - p.2 = 0 := inner_self_eq_zero.mp (hall (S p.1 - p.2))
    exact (sub_eq_zero.mp h2).symm
  · intro p hp q hq
    rw [hp.2, hq.2]
    exact hS q.1 p.1

/-- For a bounded symmetric operator on a dense core, the closure of the graph is the graph of
the everywhere-defined operator; in particular the criterion above is not vacuous. -/
