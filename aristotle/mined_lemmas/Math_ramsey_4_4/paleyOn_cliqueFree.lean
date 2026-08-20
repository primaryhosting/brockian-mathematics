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

lemma paleyOn_cliqueFree (n : ℕ) (hn : n ≤ 17) : (paleyOn n hn).CliqueFree 4 :=
  paley17_cliqueFree.comap (SimpleGraph.Embedding.comap (Fin.castLEEmb hn) paley17)

