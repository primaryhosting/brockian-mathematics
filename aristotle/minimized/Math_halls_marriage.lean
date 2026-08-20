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

theorem exists_injective_partner_of_isPerfectMatching {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∃ f : V → V, Function.Injective f ∧ ∀ v, G.Adj v (f v) := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
  choose f hf huniq using hM
  refine ⟨f, ?_, fun v => M.adj_sub (hf v)⟩
  intro v w hvw
  have hv : M.Adj (f v) v := (hf v).symm
  have hw : M.Adj (f v) w := hvw ▸ (hf w).symm
  have h1 := huniq (f v) v hv
  have h2 := huniq (f v) w hw
  exact h1.trans h2.symm

/-- A matching saturating a set `s` yields an injective map sending each vertex of `s` to an
adjacent vertex. -/

theorem halls_marriage {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {p₁ p₂ : Set V} (hbip : G.IsBipartiteWith p₁ p₂) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  constructor
  · rintro ⟨M, hM⟩ s
    obtain ⟨f, hinj, hadj⟩ := exists_injective_partner_of_isPerfectMatching hM
    refine Set.ncard_le_ncard_of_injOn f (fun x hx => ?_) (hinj.injOn) (Set.toFinite _)
    exact Set.mem_biUnion hx (hadj x)
  · intro h
    exact SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hbip h

/-- **Hall's Marriage Theorem**, one-sided version: a bipartite graph has a matching saturating
the part `p₁` if and only if Hall's condition holds for all subsets of `p₁`. -/
