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

lemma cliqueFree_three_of [DecidableEq V]
    (h : ∀ a b c : V, G.Adj a b → G.Adj a c → G.Adj b c → False) : G.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp ht
  exact h a b c hab hac hbc

