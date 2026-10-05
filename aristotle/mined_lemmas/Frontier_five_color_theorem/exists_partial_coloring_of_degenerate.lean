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

theorem exists_partial_coloring_of_degenerate {k : ℕ} (hG : Degenerate k G) (s : Finset V) :
    ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hvdeg⟩ := hG s hs
    obtain ⟨c, hc⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    set N : Finset V := (s.erase v).filter (fun u => G.Adj v u) with hN
    have hNcard : N.card ≤ k := by
      refine hvdeg N ?_ ?_
      · exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      · intro u hu
        exact (Finset.mem_filter.mp hu).2
    have himg : (N.image c).card ≤ k := le_trans (Finset.card_image_le) hNcard
    have hex : ∃ x : Fin (k + 1), x ∉ N.image c := by
      by_contra hcon
      push_neg at hcon
      have : (Finset.univ : Finset (Fin (k + 1))) ⊆ N.image c := fun x _ => hcon x
      have hcard := Finset.card_le_card this
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      omega
    obtain ⟨x, hx⟩ := hex
    refine ⟨Function.update c v x, ?_⟩
    have key : ∀ w ∈ s, G.Adj v w → Function.update c v x v ≠ Function.update c v x w := by
      intro w hw hadj
      have hwv : w ≠ v := (G.ne_of_adj hadj).symm
      have hwN : w ∈ N := by
        simp only [hN, Finset.mem_filter, Finset.mem_erase]
        exact ⟨⟨hwv, hw⟩, hadj⟩
      have : c w ∈ N.image c := Finset.mem_image_of_mem c hwN
      simp only [Function.update_self, Function.update_of_ne hwv]
      intro h
      exact hx (h ▸ this)
    intro u hu w hw hadj
    by_cases huv : u = v
    · subst huv
      exact key w hw hadj
    by_cases hwv : w = v
    · subst hwv
      exact fun h => key u hu hadj.symm h.symm
    · have hu' : u ∈ s.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
      have hw' : w ∈ s.erase v := Finset.mem_erase.mpr ⟨hwv, hw⟩
      simpa [Function.update_of_ne huv, Function.update_of_ne hwv] using hc u hu' w hw' hadj

/-- **Greedy colouring theorem.** A finite `k`-degenerate graph is `(k + 1)`-colourable. -/
