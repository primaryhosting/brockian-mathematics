import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Function

namespace Math

variable {L R : Type*}

/-- The bipartite graph on `L ⊕ R` whose edges are exactly the pairs `(a, b)` with `r a b`,
where `a : L` is a left vertex and `b : R` is a right vertex. -/

@[simp] lemma bipartiteGraph_not_adj_inr_inr (r : L → R → Prop) (b b' : R) :
    ¬ (bipartiteGraph r).Adj (.inr b) (.inr b') := id

/-- A bipartite graph given by `r` has a perfect matching iff there is a bijection
`e : L ≃ R` with `r a (e a)` for all `a`. -/
