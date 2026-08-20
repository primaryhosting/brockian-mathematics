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

lemma compl_isNClique_of_neighbors [DecidableEq V] {v : V} {t : Finset V} {n : ℕ}
    (htn : t.card = n) (hadj : ∀ w ∈ t, G.Adj v w) (h3 : G.CliqueFree 3) :
    Gᶜ.IsNClique n t := by
  refine isNClique_compl_of htn ?_
  intro a ha b hb hab hadjab
  exact h3 {v, a, b} (is3Clique_triple_iff.mpr ⟨hadj a ha, hadj b hb, hadjab⟩)

