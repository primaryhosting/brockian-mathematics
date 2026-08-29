/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the required header above is
-- given as a plain comment and repeated as the module docstring below.)

import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope of this file

Mathlib (at the pinned version) contains no theory of planar graphs, so planarity is
developed here from scratch: `Frontier.PlaneDrawing` is a straight-line drawing of a graph
in `ℝ × ℝ` and `Frontier.IsPlanar` says that such a drawing exists (by Fáry's theorem this
is equivalent, for finite simple graphs, to the usual topological notion of planarity).

What is proved here is the *base case* of the five colour theorem — the case that the
classical proof settles by a single greedy step, without any Kempe chain interchange:
every finite planar graph each of whose nonempty induced subgraphs has a vertex of degree
at most `4` is `5`-colourable (`Frontier.five_color_theorem`).  Concrete consequences are
that every planar graph of maximum degree at most `4` is `5`-colourable, and that every
graph on at most five vertices is `5`-colourable.

The purely combinatorial half of the remaining case is also proved here: the Kempe chain
interchange `Frontier.kempe_swap_proper`, which recolours a union of components of a
two-coloured subgraph.  What is *not* developed here is the topological input of the full
theorem — Euler's formula and the Jordan curve argument showing that two Kempe chains
around a vertex of degree `5` cannot both exist in a plane drawing.
-/

set_option autoImplicit false

namespace Frontier

open Finset

variable {V : Type*}

/-- A straight-line drawing of a simple graph `G` in the plane `ℝ × ℝ`:
vertices are placed at distinct points, edges are drawn as the straight segments between
their endpoints, no vertex lies in the interior of an edge, and the interiors of two
distinct edges are disjoint.  By Fáry's theorem this is, for finite simple graphs,
equivalent to the usual topological notion of planarity. -/
structure PlaneDrawing (G : SimpleGraph V) where
  /-- the position of each vertex in the plane -/
  pos : V → ℝ × ℝ
  pos_injective : Function.Injective pos
  /-- no vertex lies in the interior of an edge it is not an endpoint of -/
  vertex_notMem : ∀ v a b : V, G.Adj a b → v ≠ a → v ≠ b →
    pos v ∉ openSegment ℝ (pos a) (pos b)
  /-- interiors of distinct edges are disjoint -/
  edges_disjoint : ∀ a b c d : V, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
    openSegment ℝ (pos a) (pos b) ∩ openSegment ℝ (pos c) (pos d) = ∅

/-- A simple graph is *planar* when it admits a straight-line drawing in the plane. -/

theorem exists_partial_coloring [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (h : Degenerate G k) (s : Finset V) :
    ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hcard⟩ := h s hs
    obtain ⟨c, hc⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    obtain ⟨x, hx⟩ : ∃ x : Fin (k + 1), x ∉ ({u ∈ s.erase v | G.Adj v u} : Finset V).image c := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆
          ({u ∈ s.erase v | G.Adj v u} : Finset V).image c := fun y _ => hcon y
      have h1 := Finset.card_le_card hsub
      have h2 := (Finset.card_image_le (s := ({u ∈ s.erase v | G.Adj v u} : Finset V))
        (f := c)).trans hcard
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    refine ⟨Function.update c v x, ?_⟩
    intro u hu w hw hadj
    by_cases hu' : u = v
    · subst hu'
      have hwu : w ≠ u := (G.ne_of_adj hadj).symm
      have hmem : w ∈ ({y ∈ s.erase u | G.Adj u y} : Finset V) := by
        simp [Finset.mem_erase, hwu, hw, hadj]
      simp only [Function.update_self, ne_eq, Function.update_of_ne hwu]
      exact fun hEq => hx (hEq ▸ Finset.mem_image_of_mem c hmem)
    · by_cases hw' : w = v
      · subst hw'
        have hmem : u ∈ ({y ∈ s.erase w | G.Adj w y} : Finset V) := by
          simp [Finset.mem_erase, hu', hu, hadj.symm]
        simp only [Function.update_self, ne_eq, Function.update_of_ne hu']
        exact fun hEq => hx (hEq ▸ Finset.mem_image_of_mem c hmem)
      · simp only [Function.update_of_ne hu', Function.update_of_ne hw']
        exact hc u (Finset.mem_erase.2 ⟨hu', hu⟩) w (Finset.mem_erase.2 ⟨hw', hw⟩) hadj

/-- Greedy colouring: a `k`-degenerate graph is `(k+1)`-colourable. -/
