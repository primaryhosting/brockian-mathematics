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

lemma ramsey_4_3 (hc : 9 ≤ Fintype.card V) (h4 : G.CliqueFree 4) :
    ∃ t : Finset V, Gᶜ.IsNClique 3 t := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨t, ht⟩ := ramsey_3_4 (G := Gᶜ) hc hcon
  rw [compl_compl] at ht
  exact h4 t ht

/-- `R(4,4) ≤ 18`. -/
