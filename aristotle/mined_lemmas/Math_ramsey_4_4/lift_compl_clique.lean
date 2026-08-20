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

private lemma lift_compl_clique {s : Set V} {n : ℕ} {t : Finset s}
    (ht : ((G.induce s)ᶜ).IsNClique n t) :
    ∃ u : Finset V, (∀ x ∈ u, x ∈ s) ∧ Gᶜ.IsNClique n u := by
  rw [← induce_compl] at ht
  exact exists_isNClique_of_induce ht

/-- `R(3,3) ≤ 6`. -/
