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

lemma isNClique_compl_of [DecidableEq V] {t : Finset V} {n : ℕ} (htn : t.card = n)
    (h : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ G.Adj a b) : Gᶜ.IsNClique n t := by
  refine ⟨?_, htn⟩
  intro a ha b hb hab
  exact ⟨hab, h a (by simpa using ha) b (by simpa using hb) hab⟩

