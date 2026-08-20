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

theorem exists_injOn_partner_of_isMatching {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) {s : Set V} (hs : s ⊆ M.verts) :
    ∃ f : V → V, Set.InjOn f s ∧ ∀ v ∈ s, G.Adj v (f v) := by
  classical
  have key : ∀ v ∈ s, ∃ w, M.Adj v w ∧ ∀ y, M.Adj v y → y = w := by
    intro v hv
    obtain ⟨w, hw, huniq⟩ := hM (hs hv)
    exact ⟨w, hw, huniq⟩
  choose! f hf huniq using key
  refine ⟨f, ?_, fun v hv => M.adj_sub (hf v hv)⟩
  intro v hv w hw hvw
  have hv' : M.Adj (f v) v := (hf v hv).symm
  have hw' : M.Adj (f v) w := hvw ▸ (hf w hw).symm
  have hfv : f v ∈ M.verts := M.edge_vert hv'
  obtain ⟨u, _, hu⟩ := hM hfv
  rw [hu v hv', hu w hw']

/-- **Hall's Marriage Theorem** for bipartite graphs.

Let `G` be a bipartite graph on a finite vertex type, with parts `p₁` and `p₂`.
Then `G` admits a perfect matching if and only if Hall's condition holds, i.e. every set `s`
of vertices has at least as many neighbours as it has elements. -/
