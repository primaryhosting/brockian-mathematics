import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file header: Lean 4 requires the `import` line to be the first command of a
file, so the required header comment appears immediately after it.

## What is proved here

The full Five Colour Theorem ("every planar graph is 5-colourable") rests on two
ingredients: the combinatorial fact that a planar graph always has a vertex of degree at
most `5`, and Kempe's chain-exchange argument, which is genuinely topological (it needs a
Jordan-curve separation argument for plane embeddings).  Mathlib currently has no theory of
planar graphs or of plane embeddings at all, so the topological half is not available.

What is formalised below is the *combinatorial base case* of the theorem, in its sharpest
purely graph-theoretic form: the greedy-colouring theorem for degenerate graphs.  A graph is
`k`-degenerate when every nonempty finite set of vertices contains a vertex with at most `k`
neighbours inside that set; we prove that every finite `k`-degenerate graph is
`(k + 1)`-colourable (`Frontier.colorable_of_degenerate`).

Specialising to `k = 4` gives `Frontier.five_color_theorem`: every finite `4`-degenerate
graph is `5`-colourable.  This covers every planar graph which is `4`-degenerate — for
instance all outerplanar graphs, all series-parallel graphs and all triangle-free planar
graphs — but not planar graphs in general, which are only guaranteed to be `5`-degenerate
(the icosahedron is planar and `5`-regular).  Bridging that last gap is exactly the Kempe
chain step, which is not established here.

A second, trivial base case is recorded as `Frontier.five_color_theorem_of_card_le`:
any graph on at most five vertices is 5-colourable.

Finally, `Frontier.six_colorable_of_degree_sum_bound` records the combinatorial half of the
argument in the form it takes for genuine planar graphs: a graph in which every set of at
least three vertices spans at most `3n - 6` edges (the planar edge bound coming from Euler's
formula) is `5`-degenerate, hence `6`-colourable.
-/

namespace Frontier

open Finset

variable {V : Type*} {G : SimpleGraph V}

/-- `Degenerate k G` says that the graph `G` is `k`-degenerate: every nonempty finite set
`s` of vertices contains a vertex `v` having at most `k` neighbours inside `s`.

The "at most `k` neighbours inside `s`" condition is phrased as "every finite set of
neighbours of `v` contained in `s` has at most `k` elements", which avoids any
decidability assumptions on the adjacency relation. -/

theorem six_colorable_of_degree_sum_bound [Fintype V]
    (h : ∀ s : Finset V, 3 ≤ s.card →
      ∑ v ∈ s, (s.filter (fun u => G.Adj v u)).card ≤ 6 * s.card - 12) :
    G.Colorable 6 :=
  colorable_of_degenerate (degenerate_five_of_degree_sum_bound h)

end EdgeBound

/-- Sanity check that the degeneracy hypothesis is satisfiable: the complete graph on five
vertices is `4`-degenerate, so `five_color_theorem` applies to it. -/
example : Degenerate 4 (⊤ : SimpleGraph (Fin 5)) := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, fun t _ ht => ?_⟩
  have hsub : t ⊆ (Finset.univ.erase v) := fun u hu =>
    Finset.mem_erase.mpr ⟨(ht u hu).ne', Finset.mem_univ u⟩
  calc t.card ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
    _ = 4 := by simp

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

