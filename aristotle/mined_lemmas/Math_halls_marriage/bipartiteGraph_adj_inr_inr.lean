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

/-- **Hall's Marriage Theorem** for a bipartite graph.

The bipartite graph is given by its adjacency relation `r : V → W → Prop` between the two
(finite) sides `V` and `W`.  A *matching saturating `V`* is an injective function `f : V → W`
with `v` adjacent to `f v` for every `v : V`.

Such a matching exists if and only if *Hall's condition* holds: every set `A` of vertices of
`V` has at least `#A` neighbours in `W`.

This is Mathlib's `Fintype.all_card_le_filter_rel_iff_exists_injective`. -/

@[simp] lemma bipartiteGraph_adj_inr_inr {V W : Type*} (r : V → W → Prop) (w w' : W) :
    ¬ (bipartiteGraph r).Adj (.inr w) (.inr w') := id

/-- From a perfect matching of the bipartite graph one extracts an injective map `V → W`
picking, for each `v`, its partner. -/
