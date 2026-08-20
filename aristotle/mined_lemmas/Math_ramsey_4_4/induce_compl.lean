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

lemma induce_compl (G : SimpleGraph V) (s : Set V) : (Gᶜ).induce s = (G.induce s)ᶜ := by
  ext a b
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/-- A clique of an induced subgraph gives a clique of the ambient graph inside the set. -/
