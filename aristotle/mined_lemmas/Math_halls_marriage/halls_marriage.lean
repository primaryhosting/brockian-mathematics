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

theorem halls_marriage {V W : Type*} [Fintype V] [Fintype W] (r : V → W → Prop)
    [DecidableRel r] :
    (∀ A : Finset V, #A ≤ #{w | ∃ v ∈ A, r v w}) ↔
      ∃ f : V → W, Function.Injective f ∧ ∀ v, r v (f v) :=
  Fintype.all_card_le_filter_rel_iff_exists_injective r

/-- The bipartite graph on `V ⊕ W` whose edges are given by the relation `r : V → W → Prop`. -/
