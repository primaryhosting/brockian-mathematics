/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

open Finset

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s` or an independent set (a clique in the complement) of size `t`. -/

lemma isNClique_compl_iff (G : SimpleGraph V) (n : ℕ) (S : Finset V) :
    Gᶜ.IsNClique n S ↔ ((S : Set V).Pairwise fun a b => ¬ G.Adj a b) ∧ S.card = n := by
  rw [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a ha b hb hab => ((SimpleGraph.compl_adj _ _ _).1 (h1 ha hb hab)).2, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a ha b hb hab => (SimpleGraph.compl_adj _ _ _).2 ⟨hab, h1 ha hb hab⟩, h2⟩

