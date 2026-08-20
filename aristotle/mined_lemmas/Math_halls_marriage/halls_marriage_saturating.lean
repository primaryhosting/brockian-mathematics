import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
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

namespace Math

open Function SimpleGraph

/-- From a perfect matching one extracts a partner function: an involution-free choice of
the unique `M`-neighbour of each vertex. -/

theorem halls_marriage_saturating {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {p₁ p₂ : Set V} (hbip : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hverts, hM⟩ s hs
    obtain ⟨f, hinj, hadj⟩ := exists_injOn_partner_of_isMatching hM (hs.trans hverts)
    refine Set.ncard_le_ncard_of_injOn f (fun x hx => ?_) hinj (Set.toFinite _)
    exact Set.mem_biUnion hx (hadj x hx)
  · intro h
    exact SimpleGraph.exists_isMatching_of_forall_ncard_le hbip h

end Math

