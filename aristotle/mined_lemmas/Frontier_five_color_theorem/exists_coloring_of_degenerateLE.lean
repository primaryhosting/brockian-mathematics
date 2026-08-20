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

set_option grind.warning false

/-!
# Planar graphs and colourings

This file sets up a faithful (topological) notion of planarity for simple graphs — a
drawing of the graph in the plane `ℝ × ℝ` where vertices are distinct points and edges
are arcs meeting only at common endpoints — and proves a base case of the five colour
theorem.
-/

namespace SimpleGraph

variable {V : Type*}

/-- A drawing of a simple graph `G` in the plane: an injective placement of the vertices
as points of `ℝ × ℝ`, together with, for every edge, an arc (a continuous injective image
of the unit interval) joining the two endpoints, such that two distinct arcs meet only in
the images of their common endpoints, and a vertex point lies on an arc only if it is an
endpoint of the corresponding edge. -/
structure PlanarEmbedding (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  point : V → ℝ × ℝ
  /-- Distinct vertices get distinct points. -/
  point_inj : Function.Injective point
  /-- The set of points of the plane covered by the arc drawn for an edge. -/
  arc : Sym2 V → Set (ℝ × ℝ)
  /-- Each edge is drawn as an arc: a continuous injective image of `[0,1]` whose
  endpoints are the points of the two ends of the edge. -/
  arc_isArc : ∀ e ∈ G.edgeSet, ∃ f : unitInterval → ℝ × ℝ,
    Continuous f ∧ Function.Injective f ∧ Set.range f = arc e ∧
      Sym2.map point e = s(f 0, f 1)
  /-- Two distinct arcs meet only at points of common endpoints. -/
  arc_inter : ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, e ≠ e' →
    arc e ∩ arc e' ⊆ point '' {v | v ∈ e ∧ v ∈ e'}
  /-- A vertex point lying on an arc must be an endpoint of that edge. -/
  point_mem_arc : ∀ e ∈ G.edgeSet, ∀ v : V, point v ∈ arc e → v ∈ e

/-- A simple graph is *planar* if it can be drawn in the plane. -/

theorem exists_coloring_of_degenerateLE {G : SimpleGraph V} {k : ℕ} (h : G.DegenerateLE k)
    (s : Finset V) :
    ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hcard⟩ := h s hs
    obtain ⟨c, hc⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    set N : Finset V := (s.erase v).filter (fun w => G.Adj v w) with hN
    have him : (N.image c).card ≤ k := le_trans (Finset.card_image_le) hcard
    obtain ⟨col, hcol⟩ : ∃ col : Fin (k + 1), col ∉ N.image c := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆ N.image c := fun x _ => hcon x
      have := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hmemN : ∀ w ∈ s, w ≠ v → G.Adj v w → c w ∈ N.image c := by
      intro w hw hwv hadj
      exact Finset.mem_image_of_mem c (Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hwv, hw⟩, hadj⟩)
    refine ⟨Function.update c v col, ?_⟩
    intro u hu w hw hadj
    have hne : u ≠ w := G.ne_of_adj hadj
    by_cases huv : u = v
    · subst huv
      have hwu : w ≠ u := fun h => hne h.symm
      rw [Function.update_self, Function.update_of_ne hwu]
      intro hEq
      exact hcol (hEq ▸ hmemN w hw hwu hadj)
    · by_cases hwv : w = v
      · subst hwv
        rw [Function.update_self, Function.update_of_ne huv]
        intro hEq
        exact hcol (hEq ▸ hmemN u hu huv hadj.symm)
      · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
        exact hc u (Finset.mem_erase.2 ⟨huv, hu⟩) w (Finset.mem_erase.2 ⟨hwv, hw⟩) hadj

/-- Every `k`-degenerate graph on a finite vertex type is `(k+1)`-colourable. -/
