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

@[simp] lemma bipartiteGraph_not_adj_inl_inl (r : L → R → Prop) (a a' : L) :
    ¬ (bipartiteGraph r).Adj (.inl a) (.inl a') := id

