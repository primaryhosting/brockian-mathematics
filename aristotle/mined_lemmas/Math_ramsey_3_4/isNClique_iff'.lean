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

lemma isNClique_iff' (G : SimpleGraph V) (n : ℕ) (S : Finset V) :
    G.IsNClique n S ↔ ((S : Set V).Pairwise G.Adj) ∧ S.card = n := by
  rw [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]

/-- A triple `{a, b, c}` is pairwise `r`-related as soon as the three relevant pairs are. -/
