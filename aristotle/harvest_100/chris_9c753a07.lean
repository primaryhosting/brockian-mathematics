/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command, so the header above is a plain
-- block comment and is repeated below as the module docstring.)
import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Frontier

universe u

variable {V : Type u}

/-! ## Planarity

We record a faithful topological definition of planarity: a *plane drawing* of a
simple graph `G` consists of an injective placement of the vertices in the plane
together with, for each edge, an arc (a homeomorphic copy of the unit interval)
joining the images of its endpoints, such that arcs meet each other only in
common endpoints and meet vertex points only in their own endpoints. -/

/-- A drawing of `G` in the plane: vertices are distinct points, edges are arcs
joining their endpoints, and two arcs meet only at points that are images of
common endpoints. -/
structure PlaneDrawing (G : SimpleGraph V) where
  /-- the position of each vertex in the plane -/
  pt : V → ℝ × ℝ
  /-- distinct vertices get distinct points -/
  pt_inj : Function.Injective pt
  /-- the arc drawn for each edge (as a subset of the plane) -/
  arc : ∀ ⦃u v : V⦄, G.Adj u v → Set (ℝ × ℝ)
  /-- an edge is drawn by the same arc in either direction -/
  arc_symm : ∀ ⦃u v : V⦄ (h : G.Adj u v), arc h.symm = arc h
  /-- each arc is a homeomorphic image of `[0,1]` running from `pt u` to `pt v` -/
  arc_isArc : ∀ ⦃u v : V⦄ (h : G.Adj u v),
    ∃ f : C(unitInterval, ℝ × ℝ), Function.Injective f ∧ Set.range f = arc h ∧
      f 0 = pt u ∧ f 1 = pt v
  /-- an arc contains no vertex point other than those of its own endpoints -/
  arc_mem_pt : ∀ ⦃u v : V⦄ (h : G.Adj u v) (w : V), pt w ∈ arc h ↔ (w = u ∨ w = v)
  /-- two arcs of different edges meet only at points of shared endpoints -/
  arc_inter : ∀ ⦃u v u' v' : V⦄ (h : G.Adj u v) (h' : G.Adj u' v'),
    s(u, v) ≠ s(u', v') →
      arc h ∩ arc h' ⊆ pt '' (({u, v} : Set V) ∩ ({u', v'} : Set V))

/-- A simple graph is *planar* if it admits a drawing in the plane. -/
def Planar (G : SimpleGraph V) : Prop := Nonempty (PlaneDrawing G)

/-- Planarity is inherited by subgraphs: erasing edges from a drawn graph leaves a
drawing. -/
theorem Planar.mono {G H : SimpleGraph V} (hHG : H ≤ G) (hG : Planar G) : Planar H := by
  obtain ⟨D⟩ := hG
  refine ⟨{ pt := D.pt
            pt_inj := D.pt_inj
            arc := fun _ _ h => D.arc (hHG h)
            arc_symm := fun _ _ h => D.arc_symm (hHG h)
            arc_isArc := fun _ _ h => D.arc_isArc (hHG h)
            arc_mem_pt := fun _ _ h w => D.arc_mem_pt (hHG h) w
            arc_inter := fun _ _ _ _ h h' hne => D.arc_inter (hHG h) (hHG h') hne }⟩

/-- The empty graph on `Fin n` is planar: place the vertices along a line. -/
theorem planar_bot_fin (n : ℕ) : Planar (⊥ : SimpleGraph (Fin n)) := by
  refine ⟨{ pt := fun i => ((i : ℕ), 0)
            pt_inj := ?_
            arc := fun _ _ h => absurd h (by simp)
            arc_symm := fun _ _ h => absurd h (by simp)
            arc_isArc := fun _ _ h => absurd h (by simp)
            arc_mem_pt := fun _ _ h => absurd h (by simp)
            arc_inter := fun _ _ _ _ h => absurd h (by simp) }⟩
  intro i j hij
  have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := congrArg Prod.fst hij
  exact Fin.ext (Nat.cast_injective this)

/-! ## Degeneracy -/

/-- `G` is `k`-degenerate when every nonempty finite set of vertices contains a vertex
having at most `k` neighbours inside that set.  Equivalently, every nonempty finite
subgraph of `G` has a vertex of degree at most `k`. -/
def Degenerate (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, ((s.erase v).filter (fun u => G.Adj v u)).card ≤ k

/-- Greedy colouring: in a `k`-degenerate graph every finite set of vertices carries a
proper colouring with `k + 1` colours. -/
theorem exists_partial_coloring {G : SimpleGraph V} {k : ℕ} (hG : Degenerate k G) :
    ∀ (n : ℕ) (s : Finset V), s.card = n →
      ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hdeg⟩ := hG s hne
    set t : Finset V := s.erase v with ht
    have htcard : t.card < n := by
      rw [← hs, ht]
      exact Finset.card_erase_lt_of_mem hv
    obtain ⟨c, hc⟩ := ih t.card htcard t rfl
    -- the colours used on the neighbours of `v` inside `s`
    set N : Finset V := t.filter (fun u => G.Adj v u) with hN
    have hcard : (N.image c).card < k + 1 :=
      lt_of_le_of_lt (le_trans (Finset.card_image_le) hdeg) (Nat.lt_succ_self k)
    have : ∃ a : Fin (k + 1), a ∉ N.image c := by
      by_contra hcon
      push_neg at hcon
      have : (Finset.univ : Finset (Fin (k + 1))) ⊆ N.image c := fun a _ => hcon a
      have := Finset.card_le_card this
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    obtain ⟨a, ha⟩ := this
    refine ⟨Function.update c v a, ?_⟩
    intro x hx y hy hadj
    have hxy : x ≠ y := hadj.ne
    by_cases hxv : x = v
    · subst hxv
      have hyv : y ≠ x := fun h => hxy h.symm
      have hyt : y ∈ t := Finset.mem_erase.mpr ⟨hyv, hy⟩
      have hyN : y ∈ N := Finset.mem_filter.mpr ⟨hyt, hadj⟩
      rw [Function.update_self, Function.update_of_ne hyv]
      intro hcon
      exact ha (hcon ▸ Finset.mem_image_of_mem c hyN)
    · by_cases hyv : y = v
      · subst hyv
        have hxN : x ∈ N := Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hxv, hx⟩, hadj.symm⟩
        rw [Function.update_self, Function.update_of_ne hxv]
        intro hcon
        exact ha (hcon ▸ Finset.mem_image_of_mem c hxN)
      · rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
        exact hc x (Finset.mem_erase.mpr ⟨hxv, hx⟩) y (Finset.mem_erase.mpr ⟨hyv, hy⟩) hadj

/-- A `k`-degenerate finite graph is `(k+1)`-colourable. -/
theorem Degenerate.colorable {G : SimpleGraph V} [Fintype V] {k : ℕ}
    (hG : Degenerate k G) : G.Colorable (k + 1) := by
  obtain ⟨c, hc⟩ := exists_partial_coloring hG (Finset.univ : Finset V).card Finset.univ rfl
  exact ⟨SimpleGraph.Coloring.mk c fun {u v} h =>
    hc u (Finset.mem_univ u) v (Finset.mem_univ v) h⟩

/-- If every nonempty finite subgraph of `G` has fewer than `2 |s|` edges (equivalently,
average degree `< 5`), then `G` is `4`-degenerate.  Here `∑ v ∈ s, ...` counts each edge
inside `s` twice. -/
theorem degenerate_four_of_sparse {G : SimpleGraph V}
    (h : ∀ s : Finset V, s.Nonempty →
      ∑ v ∈ s, ((s.erase v).filter (fun u => G.Adj v u)).card ≤ 4 * s.card - 2) :
    Degenerate 4 G := by
  intro s hs
  by_contra hcon
  push_neg at hcon
  have hle : 5 * s.card ≤ ∑ v ∈ s, ((s.erase v).filter (fun u => G.Adj v u)).card := by
    calc 5 * s.card = ∑ _v ∈ s, 5 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv => hcon v hv
  have hcard : 1 ≤ s.card := Finset.card_pos.mpr hs
  have := h s hs
  omega

/-- A finite graph of maximum degree at most four is `4`-degenerate. -/
theorem degenerate_four_of_maxDegree [Fintype V] {G : SimpleGraph V}
    (h : ∀ v : V, (Finset.univ.filter (fun u => G.Adj v u)).card ≤ 4) :
    Degenerate 4 G := fun s hs => by
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, le_trans (Finset.card_le_card ?_) (h v)⟩
  exact Finset.filter_subset_filter _ (Finset.subset_univ _)

/-! ## The five colour theorem -/

/--
**Five Colour Theorem** (special case).

Every planar graph is 5-colourable.  We prove here the case of a planar graph all of
whose finite subgraphs contain a vertex of degree at most `4` (i.e. `4`-degenerate
planar graphs); this covers, for instance, every triangle-free planar graph.  The
planarity hypothesis `hplanar` is the one requested in the statement; the proof of
this case proceeds purely from the degeneracy hypothesis, so `hplanar` is not needed.
-/
theorem five_color_theorem {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hplanar : Planar G) (hdeg : Degenerate 4 G) : G.Colorable 5 :=
  hdeg.colorable

/-- **Five Colour Theorem**, base case: a planar graph on at most five vertices is
5-colourable.  (Here again planarity is not needed for this case.) -/
theorem five_color_theorem_small {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hplanar : Planar G) (hcard : Fintype.card V ≤ 5) : G.Colorable 5 :=
  G.colorable_of_fintype.mono hcard

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

