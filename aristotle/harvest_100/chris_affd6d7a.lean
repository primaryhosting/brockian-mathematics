/-
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede every command, including module docstrings, so the
-- header above is repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

universe u v

/-- The Euclidean plane, in which planar graphs are drawn. -/
abbrev Plane : Type := ℝ × ℝ

/-- A (topological) planar embedding of a simple graph `G`: an injective placement of the
vertices in the plane together with, for every edge, an arc (the homeomorphic image of a
closed interval) joining its endpoints, such that

* no arc passes through a vertex other than its own endpoints, and
* two arcs belonging to distinct edges meet only in common endpoints.

This is the standard definition of a plane drawing of a graph. -/
structure PlanarEmbedding {V : Type u} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  point : V → Plane
  /-- Distinct vertices get distinct positions. -/
  point_injective : Function.Injective point
  /-- The arc drawn for the (unordered) pair `{u, v}`; only constrained when `u` and `v`
  are adjacent. -/
  arc : V → V → Set Plane
  /-- The arc only depends on the unordered pair. -/
  arc_symm : ∀ u v, arc u v = arc v u
  /-- For an edge `uv` the set `arc u v` is a simple curve from `point u` to `point v`. -/
  arc_isCurve : ∀ ⦃u v : V⦄, G.Adj u v → ∃ f : ℝ → Plane,
    ContinuousOn f (Set.Icc 0 1) ∧ Set.InjOn f (Set.Icc 0 1) ∧
      f 0 = point u ∧ f 1 = point v ∧ f '' Set.Icc 0 1 = arc u v
  /-- An arc contains no vertex other than its endpoints. -/
  arc_vertices : ∀ ⦃u v : V⦄, G.Adj u v → ∀ w : V, point w ∈ arc u v → w = u ∨ w = v
  /-- Arcs of distinct edges meet only at shared endpoints. -/
  arc_disjoint : ∀ ⦃u v x y : V⦄, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
    arc u v ∩ arc x y ⊆ point '' (({u, v} : Set V) ∩ ({x, y} : Set V))

/-- A simple graph is *planar* when it admits a plane drawing. -/
def Planar {V : Type u} (G : SimpleGraph V) : Prop := Nonempty (PlanarEmbedding G)

/-- Planarity is inherited along injective graph maps: if `H` maps injectively into a planar
graph `G` preserving adjacency, then `H` is planar. -/
theorem Planar.of_injective {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : W → V) (hf : Function.Injective f) (hmap : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (hG : Planar G) : Planar H := by
  obtain ⟨e⟩ := hG
  refine ⟨{ point := fun w => e.point (f w)
            point_injective := e.point_injective.comp hf
            arc := fun a b => e.arc (f a) (f b)
            arc_symm := fun a b => e.arc_symm _ _
            arc_isCurve := fun a b hab => e.arc_isCurve (hmap a b hab)
            arc_vertices := ?_
            arc_disjoint := ?_ }⟩
  · intro a b hab w hw
    rcases e.arc_vertices (hmap a b hab) (f w) hw with h | h
    · exact Or.inl (hf h)
    · exact Or.inr (hf h)
  · intro a b x y hab hxy hne
    have hne' : s(f a, f b) ≠ s(f x, f y) := by
      intro hEq
      rw [Sym2.eq_iff] at hEq
      refine hne ?_
      rw [Sym2.eq_iff]
      rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hf h1, hf h2⟩
      · exact Or.inr ⟨hf h1, hf h2⟩
    intro p hp
    obtain ⟨q, hq, hqp⟩ := e.arc_disjoint (hmap a b hab) (hmap x y hxy) hne' hp
    obtain ⟨hq1, hq2⟩ := hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq1 hq2
    rcases hq1 with h1 | h1 <;> rcases hq2 with h2 | h2
    · exact ⟨a, ⟨by simp, by simp [hf (h1.symm.trans h2)]⟩, by rw [← hqp, h1]⟩
    · exact ⟨a, ⟨by simp, by simp [hf (h1.symm.trans h2)]⟩, by rw [← hqp, h1]⟩
    · exact ⟨b, ⟨by simp, by simp [hf (h1.symm.trans h2)]⟩, by rw [← hqp, h1]⟩
    · exact ⟨b, ⟨by simp, by simp [hf (h1.symm.trans h2)]⟩, by rw [← hqp, h1]⟩

/-- Every subgraph of a planar graph is planar. -/
theorem Planar.subgraph {V : Type u} {G : SimpleGraph V} (hG : Planar G) (G' : G.Subgraph) :
    Planar G'.coe :=
  Planar.of_injective Subtype.val Subtype.val_injective (fun _ _ h => G'.adj_sub h) hG

/-- Planarity transfers along an equivalence of vertex types (via the comapped graph). -/
theorem Planar.comap_equiv {V : Type u} {W : Type v} {G : SimpleGraph V} (e : V ≃ W)
    (hG : Planar G) : Planar (G.comap e.symm) :=
  Planar.of_injective e.symm e.symm.injective (fun _ _ h => h) hG

/-! ### A concrete plane drawing

To see that `Frontier.Planar` is not vacuous, we exhibit an explicit plane drawing of the
complete graph on two vertices: the vertices are placed at `(0,0)` and `(1,0)` and the edge is
drawn as the segment joining them. -/

/-- The unit segment on the `x`-axis, used as the arc of the single edge of `K₂`. -/
noncomputable def unitSeg : Set Plane := (fun t : ℝ => (t, (0 : ℝ))) '' Set.Icc 0 1

/-- The placement of the two vertices of `K₂` at `(0,0)` and `(1,0)`. -/
def twoPoints : Fin 2 → Plane := fun i => (((i : ℕ) : ℝ), 0)

/-- `K₂`, the complete graph on two vertices, is planar. -/
theorem planar_completeGraph_fin_two : Planar (⊤ : SimpleGraph (Fin 2)) := by
  have hfwd : ContinuousOn (fun t : ℝ => (t, (0 : ℝ))) (Set.Icc 0 1) := by fun_prop
  have hbwd : ContinuousOn (fun t : ℝ => ((1 - t : ℝ), (0 : ℝ))) (Set.Icc 0 1) := by fun_prop
  refine ⟨{ point := twoPoints
            point_injective := ?_
            arc := fun _ _ => unitSeg
            arc_symm := fun _ _ => rfl
            arc_isCurve := ?_
            arc_vertices := ?_
            arc_disjoint := ?_ }⟩
  · intro a b hab
    have : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := congrArg Prod.fst hab
    exact Fin.ext (by exact_mod_cast this)
  · intro u v huv
    have hne : u ≠ v := huv.ne
    fin_cases u <;> fin_cases v <;> simp_all
    · refine ⟨fun t => (t, 0), hfwd, ?_, by simp [twoPoints], by simp [twoPoints], rfl⟩
      intro a _ b _ hab
      simpa using congrArg Prod.fst hab
    · refine ⟨fun t => ((1 - t : ℝ), 0), hbwd, ?_, by norm_num [twoPoints],
        by norm_num [twoPoints], ?_⟩
      · intro a _ b _ hab
        have h := congrArg Prod.fst hab
        simp only at h
        linarith
      · ext p
        simp only [unitSeg, Set.mem_image, Set.mem_Icc]
        constructor
        · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨1 - t, ⟨by linarith, by linarith⟩, by simp⟩
        · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨1 - t, ⟨by linarith, by linarith⟩, by simp⟩
  · intro u v huv w _
    have hne : u ≠ v := huv.ne
    revert hne
    fin_cases u <;> fin_cases v <;> fin_cases w <;> simp
  · intro u v x y huv hxy hne
    exact absurd (by revert hne; fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;>
      simp_all [SimpleGraph.top_adj] : s(u, v) = s(x, y)) hne

/-! ### The statement of the Four Colour Theorem -/

/-- The Four Colour Theorem for *finite* planar graphs (with vertex type in `Type 0`). -/
def FourColorTheoremFinite : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Planar G → G.Colorable 4

/-- The Four Colour Theorem: every planar graph is 4-colourable. -/
def FourColorTheorem : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V), Planar G → G.Colorable 4

/-- The finite case, stated for finite vertex types in an arbitrary universe. -/
theorem colorable_of_finite (h : FourColorTheoremFinite) {W : Type u} [Finite W]
    (H : SimpleGraph W) (hH : Planar H) : H.Colorable 4 := by
  cases nonempty_fintype W
  set n := Fintype.card W with hn
  set e : W ≃ Fin n := Fintype.equivFin W with he
  have hK : (H.comap e.symm).Colorable 4 := h (Fin n) _ (Planar.comap_equiv e hH)
  refine SimpleGraph.Colorable.of_hom (G' := H.comap e.symm) ?_ hK
  refine ⟨e, ?_⟩
  intro a b hab
  simpa [SimpleGraph.comap] using hab

/-! ### A reducible configuration: vertices of degree at most three -/

/-- **Deleting a vertex of degree at most three.** If `v` has at most three neighbours and the
graph obtained by deleting `v` is 4-colourable, then so is the whole graph: at most three
colours are forbidden at `v`, so a fourth one is available. -/
theorem colorable_of_delete_small_degree_vertex {V : Type u} [Finite V] (G : SimpleGraph V)
    (v : V) (hdeg : (G.neighborSet v).ncard ≤ 3)
    (h : (G.induce ({v}ᶜ : Set V)).Colorable 4) : G.Colorable 4 := by
  obtain ⟨C⟩ := h
  classical
  set c' : V → Fin 4 := fun w => if hw : w = v then 0 else C ⟨w, by simpa using hw⟩ with hc'
  set S : Set (Fin 4) := c' '' (G.neighborSet v) with hS
  have hfin : (G.neighborSet v).Finite := Set.toFinite _
  have hScard : S.ncard ≤ 3 := le_trans (Set.ncard_image_le hfin) hdeg
  have hz : ∃ z : Fin 4, z ∉ S := by
    by_contra hcon
    push_neg at hcon
    have huniv : S = Set.univ := Set.eq_univ_iff_forall.mpr hcon
    rw [huniv, Set.ncard_univ] at hScard
    simp at hScard
  obtain ⟨z, hzS⟩ := hz
  refine ⟨SimpleGraph.Coloring.mk (fun w => if w = v then z else c' w) ?_⟩
  intro a b hab
  by_cases ha : a = v
  · subst ha
    have hb : b ≠ a := (hab.ne).symm
    simp only [if_neg hb]
    intro hEq
    exact hzS ⟨b, hab, hEq.symm⟩
  · by_cases hb : b = v
    · subst hb
      simp only [if_neg ha]
      intro hEq
      exact hzS ⟨a, hab.symm, hEq⟩
    · simp only [if_neg ha, if_neg hb, hc', dif_neg ha, dif_neg hb]
      exact C.valid (by simpa using hab)

/-- **Reduction of the finite Four Colour Theorem to graphs of minimum degree at least four.**

A smallest counterexample has no vertex of degree `≤ 3`, since such a vertex can be deleted and
its colour restored. Hence it suffices to prove the theorem for finite planar graphs in which
every vertex has at least four neighbours. -/
theorem fourColorTheoremFinite_of_min_degree_four
    (h : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Planar G →
      (∀ v : V, 4 ≤ (G.neighborSet v).ncard) → G.Colorable 4) :
    FourColorTheoremFinite := by
  have key : ∀ n : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V ≤ n → Planar G → G.Colorable 4 := by
    intro n
    induction n with
    | zero =>
      intro V _ G hcard _
      have : IsEmpty V := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      exact SimpleGraph.Colorable.of_isEmpty 4
    | succ n ih =>
      intro V _ G hcard hplanar
      by_cases hdeg : ∃ v : V, (G.neighborSet v).ncard ≤ 3
      · obtain ⟨v, hv⟩ := hdeg
        have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
        have hcard' : Fintype.card ({v}ᶜ : Set V) ≤ n := by
          rw [Fintype.card_compl_set]
          simp only [Set.card_singleton]
          omega
        have hpl : Planar (G.induce ({v}ᶜ : Set V)) :=
          Planar.of_injective Subtype.val Subtype.val_injective (fun _ _ hab => hab) hplanar
        exact colorable_of_delete_small_degree_vertex G v hv (ih _ _ hcard' hpl)
      · push_neg at hdeg
        exact h V G hplanar (fun v => hdeg v)
  intro V _ G hplanar
  exact key (Fintype.card V) V G le_rfl hplanar

/-- **Reduction of the Four Colour Theorem to its finite case.**

If every finite planar graph is 4-colourable, then *every* planar graph (on a vertex set of
arbitrary cardinality) is 4-colourable. The proof is a compactness argument
(de Bruijn–Erdős): every finite subgraph of a planar graph is a finite planar graph. -/
theorem four_color_statement (h : FourColorTheoremFinite) : FourColorTheorem.{u} := by
  intro V G hG
  refine SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom ?_
  intro G' hfin
  have : Finite G'.verts := hfin.to_subtype
  exact (colorable_of_finite h G'.coe (hG.subgraph G')).some

end Frontier

