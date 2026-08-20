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

def bipartiteGraph {V W : Type*} (r : V → W → Prop) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | .inl v, .inr w => r v w
    | .inr w, .inl v => r v w
    | _, _ => False
  symm := by rintro (a | a) (b | b) h <;> exact h
  loopless := ⟨by rintro (a | a) h <;> exact h⟩

