/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset SimpleGraph

/-! ### Generic clique helpers -/

section Helpers
variable {V : Type*} {G : SimpleGraph V}

/-- A set with no internal `G`-edges is a clique of the complement. -/

private lemma nbrs_eq_neighborFinset (v : V) : nbrs G v = G.neighborFinset v := by
  ext w
  simp only [nbrs, Finset.mem_filter, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩, h⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Transfer a clique of the complement of an induced subgraph up to the ambient graph. -/
