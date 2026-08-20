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

lemma paleyOn_compl_cliqueFree (n : ℕ) (hn : n ≤ 17) : (paleyOn n hn)ᶜ.CliqueFree 4 := by
  rw [paleyOn, comap_compl]
  exact paley17_compl_cliqueFree.comap (SimpleGraph.Embedding.comap (Fin.castLEEmb hn) paley17ᶜ)

/-! ### The Ramsey number `R(4,4) = 18` -/

/-- **R(4,4) = 18**: `18` is the least `n` such that every graph on `n` vertices contains
either a clique of size 4 or an independent set of size 4. -/
