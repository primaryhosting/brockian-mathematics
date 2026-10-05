import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
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

namespace Math2

/-- A finite simple graph, presented as a simple graph on the vertex set `Fin n`. -/
structure FinGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency structure. -/
  adj : SimpleGraph (Fin n)

namespace FinGraph

/-- The graph obtained from `H` by contracting the edge `{a, b}`: the vertex `b` is deleted and
its neighbourhood is added to that of `a`. -/

def contract (H : FinGraph) (a b : Fin H.n) : SimpleGraph {v : Fin H.n // v ≠ b} where
  Adj u w := u ≠ w ∧
    (H.adj.Adj u.1 w.1 ∨ (u.1 = a ∧ H.adj.Adj b w.1) ∨ (w.1 = a ∧ H.adj.Adj u.1 b))
  symm := by
    rintro u w ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h1, h2.symm⟩)
    · exact Or.inr (Or.inl ⟨h1, h2.symm⟩)
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `G` embeds into `H` as a subgraph: there is an injection of vertices carrying edges to
edges.  (This single relation encodes deletion of vertices, deletion of edges, and relabelling
of vertices.) -/
