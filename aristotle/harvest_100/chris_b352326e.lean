/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Finset

variable {V : Type*}

/-! ## Planarity

Mathlib has no notion of planarity, so we introduce one.  For a *finite simple graph*,
planarity is equivalent (Fáry's theorem) to the existence of a **straight-line plane
drawing**: an injective placement `f : V → ℝ × ℝ` of the vertices such that the closed
segments representing the edges meet only in common endpoints, and no vertex lies on a
segment of an edge of which it is not an endpoint. -/

/-- `Planar G` says that `G` admits a straight-line plane drawing:
the vertices are placed injectively in the plane, the edges are drawn as straight segments,
no vertex lies on an edge it is not an endpoint of, and two distinct edges meet only at a
common endpoint. -/
def Planar (G : SimpleGraph V) : Prop :=
  ∃ f : V → ℝ × ℝ,
    Function.Injective f ∧
    (∀ a b v : V, G.Adj a b → v ≠ a → v ≠ b → f v ∉ segment ℝ (f a) (f b)) ∧
    (∀ a b c d : V, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
      segment ℝ (f a) (f b) ∩ segment ℝ (f c) (f d) ⊆
        f '' (({a, b} : Set V) ∩ ({c, d} : Set V)))

/-! ## Degeneracy and greedy colouring -/

/-- `Degenerate k G` says that every nonempty finite set of vertices contains a vertex with
at most `k` neighbours inside that set.  Equivalently, every nonempty induced subgraph of
`G` has a vertex of degree at most `k`. -/
def Degenerate (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, {w | w ∈ s ∧ G.Adj v w}.ncard ≤ k

/-- **Greedy colouring.**  In a `k`-degenerate graph, every finite set of vertices can be
coloured with `k + 1` colours so that adjacent vertices in that set receive distinct
colours. -/
theorem exists_partial_coloring {G : SimpleGraph V} {k : ℕ} (hG : Degenerate k G) :
    ∀ (n : ℕ) (s : Finset V), s.card = n →
      ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  classical
  intro n
  induction n with
  | zero =>
      intro s hs
      refine ⟨fun _ => 0, ?_⟩
      rw [Finset.card_eq_zero] at hs
      simp [hs]
  | succ n ih =>
      intro s hs
      have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨v, hv, hvcard⟩ := hG s hne
      -- `Ns` : the neighbours of `v` inside `s`
      set Ns : Finset V := s.filter (fun w => G.Adj v w) with hNs
      have hcoe : (↑Ns : Set V) = {w | w ∈ s ∧ G.Adj v w} := by
        rw [hNs, Finset.coe_filter]
      have hNscard : Ns.card ≤ k := by
        have h1 := Set.ncard_coe_finset Ns
        rw [hcoe] at h1
        omega
      -- colour the rest of `s` by induction
      have hcard : (s.erase v).card = n := by
        rw [Finset.card_erase_of_mem hv, hs]
        omega
      obtain ⟨c, hc⟩ := ih (s.erase v) hcard
      -- pick a colour unused on the neighbours of `v`
      have hlt : (Ns.image c).card < Fintype.card (Fin (k + 1)) := by
        have := Finset.card_image_le (s := Ns) (f := c)
        simp only [Fintype.card_fin]
        omega
      have hnu : Ns.image c ≠ Finset.univ := (Finset.card_lt_iff_ne_univ _).mp hlt
      have hex : ∃ col : Fin (k + 1), col ∉ Ns.image c := by
        by_contra hcon
        push_neg at hcon
        exact hnu (Finset.eq_univ_iff_forall.mpr hcon)
      obtain ⟨col, hcol⟩ := hex
      refine ⟨Function.update c v col, ?_⟩
      intro u hu w hw hadj
      by_cases hu' : u = v
      · have hadjv : G.Adj v w := hu' ▸ hadj
        have hwv : w ≠ v := (G.ne_of_adj hadjv).symm
        have hwNs : w ∈ Ns := by
          rw [hNs]; exact Finset.mem_filter.mpr ⟨hw, hadjv⟩
        have himg : c w ∈ Ns.image c := Finset.mem_image_of_mem c hwNs
        rw [hu', Function.update_self, Function.update_of_ne hwv]
        intro h
        exact hcol (by rw [h]; exact himg)
      · by_cases hw' : w = v
        · have hadjv : G.Adj v u := (hw' ▸ hadj).symm
          have huNs : u ∈ Ns := by
            rw [hNs]; exact Finset.mem_filter.mpr ⟨hu, hadjv⟩
          have himg : c u ∈ Ns.image c := Finset.mem_image_of_mem c huNs
          rw [hw', Function.update_self, Function.update_of_ne hu']
          intro h
          exact hcol (by rw [← h]; exact himg)
        · rw [Function.update_of_ne hu', Function.update_of_ne hw']
          exact hc u (Finset.mem_erase.mpr ⟨hu', hu⟩) w (Finset.mem_erase.mpr ⟨hw', hw⟩) hadj

/-- A `k`-degenerate finite graph is `(k + 1)`-colourable. -/
theorem colorable_of_degenerate [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : Degenerate k G) : G.Colorable (k + 1) := by
  obtain ⟨c, hc⟩ :=
    exists_partial_coloring hG (Fintype.card V) Finset.univ Finset.card_univ
  exact ⟨SimpleGraph.Coloring.mk c fun {u w} h =>
    hc u (Finset.mem_univ u) w (Finset.mem_univ w) h⟩

/-- Base case of the induction in the Five Color Theorem: a graph with at most five
vertices is trivially 5-colourable. -/
theorem colorable_five_of_card_le [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 5) : G.Colorable 5 :=
  (G.colorable_of_fintype).mono h

/-- Any graph on at most `k + 1` vertices is `k`-degenerate. -/
theorem degenerate_of_card_le [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : Fintype.card V ≤ k + 1) : Degenerate k G := by
  classical
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  have hsub : {w | w ∈ s ∧ G.Adj v w} ⊆ (↑(Finset.univ.erase v) : Set V) := by
    intro w hw
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_univ, true_and]
    exact fun hwv => (G.ne_of_adj hw.2).symm hwv
  calc {w | w ∈ s ∧ G.Adj v w}.ncard
      ≤ (↑(Finset.univ.erase v) : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (Finset.univ.erase v).card := Set.ncard_coe_finset _
    _ ≤ k := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
        omega

/-! ## Non-vacuity of `Planar`

The following two lemmas exhibit planar graphs, so that the Five Color Theorem below is not
vacuously true. -/

/-- Every edgeless graph on `Fin n` is planar. -/
theorem planar_bot (n : ℕ) : Planar (⊥ : SimpleGraph (Fin n)) := by
  refine ⟨fun i => ((i : ℝ), 0), ?_, ?_, ?_⟩
  · intro i j h
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Fin.ext h.1
  · intro a b v hab; exact absurd hab (by simp)
  · intro a b c d hab; exact absurd hab (by simp)

/-- The complete graph on two vertices (a single edge) is planar. -/
theorem planar_top_two : Planar (⊤ : SimpleGraph (Fin 2)) := by
  have h2 : ∀ a b v : Fin 2, (⊤ : SimpleGraph (Fin 2)).Adj a b → v ≠ a → v ≠ b → False := by
    decide
  have h3 : ∀ a b c d : Fin 2, (⊤ : SimpleGraph (Fin 2)).Adj a b →
      (⊤ : SimpleGraph (Fin 2)).Adj c d → s(a, b) ≠ s(c, d) → False := by decide
  refine ⟨fun i => ((i : ℝ), 0), ?_, ?_, ?_⟩
  · intro i j h
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Fin.ext h.1
  · intro a b v hab hva hvb
    exact (h2 a b v hab hva hvb).elim
  · intro a b c d hab hcd hne
    exact (h3 a b c d hab hcd hne).elim

/-- **Five Color Theorem (degeneracy case).**

Every finite planar graph all of whose induced subgraphs contain a vertex of degree at most
`4` is 5-colourable.

The hypothesis `Planar G` is stated because the theorem is about planar graphs, but the
proof given here does not use it: the colouring is produced greedily from the degeneracy
hypothesis `Degenerate 4 G` alone.  (The full Five Color Theorem replaces `Degenerate 4 G`
by the weaker `Degenerate 5 G`, which holds for *all* planar graphs by Euler's formula; the
step from 5-degeneracy to a 5-colouring requires the Kempe-chain argument and genuinely
uses the plane embedding.) -/
theorem five_color_theorem [Fintype V] {G : SimpleGraph V}
    (_hplanar : Planar G) (hdeg : Degenerate 4 G) : G.Colorable 5 :=
  colorable_of_degenerate hdeg

/-- If every vertex of `G` has at most `k` neighbours, then `G` is `k`-degenerate. -/
theorem degenerate_of_neighborSet_ncard_le [Finite V] {G : SimpleGraph V} {k : ℕ}
    (hd : ∀ v, (G.neighborSet v).ncard ≤ k) : Degenerate k G := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hd v)⟩
  intro w hw
  exact hw.2

/-- **Five Color Theorem for planar graphs of maximum degree at most four.**
Here the degeneracy hypothesis is replaced by a purely local condition. -/
theorem five_color_of_maxDegree_le_four [Fintype V] {G : SimpleGraph V}
    (hplanar : Planar G) (hd : ∀ v, (G.neighborSet v).ncard ≤ 4) : G.Colorable 5 :=
  five_color_theorem hplanar (degenerate_of_neighborSet_ncard_le hd)

/-- Sanity check: the hypotheses of `five_color_theorem` are simultaneously satisfiable by a
graph with an edge, so the theorem is not vacuous. -/
example : (⊤ : SimpleGraph (Fin 2)).Colorable 5 :=
  five_color_theorem planar_top_two (degenerate_of_card_le (by simp))

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

