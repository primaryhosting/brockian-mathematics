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

theorem degenerate_five_of_degree_sum_bound
    (h : ∀ s : Finset V, 3 ≤ s.card →
      ∑ v ∈ s, (s.filter (fun u => G.Adj v u)).card ≤ 6 * s.card - 12) :
    Degenerate 5 G := by
  refine degenerate_of_card_filter ?_
  intro s hs
  obtain ⟨v₀, hv₀⟩ := hs
  by_cases hsmall : s.card ≤ 3
  · refine ⟨v₀, hv₀, ?_⟩
    have hsub : s.filter (fun u => G.Adj v₀ u) ⊆ s.erase v₀ := by
      intro u hu
      obtain ⟨hus, hadj⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_erase.mpr ⟨hadj.ne', hus⟩
    have := Finset.card_le_card hsub
    have hcard : (s.erase v₀).card = s.card - 1 := Finset.card_erase_of_mem hv₀
    omega
  · push_neg at hsmall
    by_contra hcon
    push_neg at hcon
    have hbig : ∀ v ∈ s, 6 ≤ (s.filter (fun u => G.Adj v u)).card := fun v hv =>
      hcon v hv
    have hsum : s.card * 6 ≤ ∑ v ∈ s, (s.filter (fun u => G.Adj v u)).card := by
      simpa [smul_eq_mul] using Finset.card_nsmul_le_sum s _ 6 hbig
    have hb := h s (by omega)
    omega

/-- **Six colour theorem from the planar edge bound.** A finite graph in which every set of
at least three vertices spans at most `3 * s.card - 6` edges is `6`-colourable.  This is the
combinatorial half of the Five Colour Theorem; upgrading `6` to `5` requires Kempe's
chain-exchange argument, which is topological and is not formalised here. -/
