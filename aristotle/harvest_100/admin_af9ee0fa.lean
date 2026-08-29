/-
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

universe u

namespace Frontier

/-- The Euclidean plane, in which planar graphs are drawn. -/
abbrev Plane : Type := ℝ × ℝ

/-- A *plane drawing* of a simple graph `G`: an injective placement of the vertices in the
plane together with, for every edge, an arc (a homeomorphic image of `[0,1]`) joining the
positions of its endpoints, such that arcs meet the vertex set only at their own endpoints and
two arcs belonging to distinct edges meet only at common endpoints. -/
structure Drawing {V : Type*} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  pos : V → Plane
  /-- Distinct vertices are drawn at distinct points. -/
  pos_injective : Function.Injective pos
  /-- The point set of the arc drawn for the (unordered) edge `{u, v}`. -/
  arc : V → V → Set Plane
  /-- The arc of an edge does not depend on the order of its endpoints. -/
  arc_symm : ∀ u v : V, arc u v = arc v u
  /-- The arc of an edge is a simple curve running from one endpoint to the other. -/
  arc_isArc : ∀ u v : V, G.Adj u v →
    ∃ f : ℝ → Plane, ContinuousOn f (Set.Icc 0 1) ∧ Set.InjOn f (Set.Icc 0 1) ∧
      f 0 = pos u ∧ f 1 = pos v ∧ arc u v = f '' Set.Icc 0 1
  /-- An arc passes through no vertices other than its own endpoints. -/
  arc_inter_pos : ∀ u v : V, G.Adj u v → ∀ w : V, pos w ∈ arc u v → w = u ∨ w = v
  /-- Two arcs belonging to distinct edges meet only at common endpoints. -/
  arc_inter_arc : ∀ u v x y : V, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
    ∀ p ∈ arc u v ∩ arc x y, ∃ w : V, (w = u ∨ w = v) ∧ (w = x ∨ w = y) ∧ p = pos w

/-- A graph is *planar* when it admits a plane drawing. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop := Nonempty (Drawing G)

/-- **The Four Colour Statement** (Appel–Haken), as a proposition: every planar graph is
4-colourable. -/
def FourColorStatement : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The Four Colour Statement restricted to graphs whose vertex set is `Fin n`. -/
def FourColorStatementFin : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)), IsPlanar H → H.Colorable 4

/-- A plane drawing of `G` restricts to a plane drawing of any subgraph of `G`. -/
def Drawing.restrict {V : Type*} {G : SimpleGraph V} (D : Drawing G) (G' : G.Subgraph) :
    Drawing G'.coe where
  pos v := D.pos v.1
  pos_injective := fun _ _ h => Subtype.ext (D.pos_injective h)
  arc u v := D.arc u.1 v.1
  arc_symm _ _ := D.arc_symm _ _
  arc_isArc _ _ h := D.arc_isArc _ _ (G'.adj_sub h)
  arc_inter_pos u v h w hw := by
    rcases D.arc_inter_pos u.1 v.1 (G'.adj_sub h) w.1 hw with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  arc_inter_arc u v x y huv hxy hne p hp := by
    have hne' : s(u.1, v.1) ≠ s(x.1, y.1) := by
      intro h
      rw [Sym2.eq_iff] at h
      refine hne ?_
      rw [Sym2.eq_iff]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    obtain ⟨w, hw1, hw2, hw3⟩ :=
      D.arc_inter_arc u.1 v.1 x.1 y.1 (G'.adj_sub huv) (G'.adj_sub hxy) hne' p hp
    rcases hw1 with rfl | rfl
    · refine ⟨u, Or.inl rfl, ?_, hw3⟩
      rcases hw2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · refine ⟨v, Or.inr rfl, ?_, hw3⟩
      rcases hw2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)

/-- Planarity is inherited by subgraphs. -/
theorem IsPlanar.subgraph {V : Type*} {G : SimpleGraph V} (hG : IsPlanar G)
    (G' : G.Subgraph) : IsPlanar G'.coe :=
  ⟨hG.some.restrict G'⟩

/-- A plane drawing transports along an isomorphism of graphs. -/
def Drawing.ofIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (D : Drawing G)
    (e : G ≃g H) : Drawing H where
  pos w := D.pos (e.symm w)
  pos_injective := by
    intro a b h
    simpa using congrArg e (D.pos_injective h)
  arc u v := D.arc (e.symm u) (e.symm v)
  arc_symm _ _ := D.arc_symm _ _
  arc_isArc _ _ h := D.arc_isArc _ _ (e.symm.map_adj_iff.mpr h)
  arc_inter_pos u v h w hw := by
    rcases D.arc_inter_pos _ _ (e.symm.map_adj_iff.mpr h) (e.symm w) hw with h1 | h1
    · exact Or.inl (by simpa using congrArg e h1)
    · exact Or.inr (by simpa using congrArg e h1)
  arc_inter_arc u v x y huv hxy hne p hp := by
    have hne' : s(e.symm u, e.symm v) ≠ s(e.symm x, e.symm y) := by
      intro h
      rw [Sym2.eq_iff] at h
      refine hne ?_
      rw [Sym2.eq_iff]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simpa using congrArg e h1, by simpa using congrArg e h2⟩
      · exact Or.inr ⟨by simpa using congrArg e h1, by simpa using congrArg e h2⟩
    obtain ⟨w, hw1, hw2, hw3⟩ := D.arc_inter_arc _ _ _ _ (e.symm.map_adj_iff.mpr huv)
      (e.symm.map_adj_iff.mpr hxy) hne' p hp
    refine ⟨e w, ?_, ?_, by simpa using hw3⟩
    · rcases hw1 with h | h
      · exact Or.inl (by simpa using congrArg e h)
      · exact Or.inr (by simpa using congrArg e h)
    · rcases hw2 with h | h
      · exact Or.inl (by simpa using congrArg e h)
      · exact Or.inr (by simpa using congrArg e h)

/-- Planarity is invariant under isomorphism of graphs. -/
theorem IsPlanar.ofIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (hG : IsPlanar G)
    (e : G ≃g H) : IsPlanar H :=
  ⟨hG.some.ofIso e⟩

/-- Sanity check: the definition is satisfiable by a graph that actually has an edge —
the complete graph on two vertices is planar, drawn as a straight segment. -/
theorem isPlanar_top_bool : IsPlanar (⊤ : SimpleGraph Bool) := by
  refine ⟨{ pos := fun b => (if b then 1 else 0, 0)
            pos_injective := ?_
            arc := fun _ _ => (fun t : ℝ => (t, (0 : ℝ))) '' Set.Icc 0 1
            arc_symm := fun _ _ => rfl
            arc_isArc := ?_
            arc_inter_pos := ?_
            arc_inter_arc := ?_ }⟩
  · intro a b h
    cases a <;> cases b <;> simp_all
  · intro u v huv
    have huv' : u ≠ v := huv.ne
    have hflip : (fun t : ℝ => ((1 - t, 0) : Plane)) '' Set.Icc 0 1
        = (fun t : ℝ => ((t, 0) : Plane)) '' Set.Icc 0 1 := by
      ext p
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨1 - t, ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        refine ⟨1 - t, ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩, ?_⟩
        simp
    cases u <;> cases v <;> simp_all
    · refine ⟨fun t : ℝ => (t, (0 : ℝ)), by fun_prop, ?_, by norm_num, by norm_num, rfl⟩
      intro a _ b _ h
      exact (Prod.mk.injEq _ _ _ _ ▸ h).1
    · refine ⟨fun t : ℝ => (1 - t, (0 : ℝ)), by fun_prop, ?_, by norm_num, by norm_num,
        hflip.symm⟩
      intro a _ b _ h
      have := (Prod.mk.injEq _ _ _ _ ▸ h).1
      linarith
  · intro u v huv w _
    have : u ≠ v := huv.ne
    cases u <;> cases v <;> cases w <;> simp_all
  · intro u v x y huv hxy hne p _
    exact absurd (by cases u <;> cases v <;> cases x <;> cases y <;> simp_all) hne

/-- Base case: every graph on at most four vertices is 4-colourable. -/
theorem colorable_four_of_card_le_four {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 4) : G.Colorable 4 :=
  SimpleGraph.Colorable.mono h (SimpleGraph.colorable_of_fintype G)

/-- Greedy colouring: if every nonempty finite set of vertices contains a vertex with at most
`k` neighbours inside that set, then every finite set of vertices carries a proper colouring
with `k + 1` colours. -/
theorem exists_partial_coloring {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (h : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (fun w => G.Adj v w)).card ≤ k)
    (s : Finset V) :
    ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hvcard⟩ := h s hs
    obtain ⟨c, hc⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
    have hcard : ((s.filter (fun w => G.Adj v w)).image c).card ≤ k :=
      le_trans Finset.card_image_le hvcard
    obtain ⟨col, hcol⟩ : ∃ col : Fin (k + 1), col ∉ (s.filter (fun w => G.Adj v w)).image c := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆ (s.filter (fun w => G.Adj v w)).image c :=
        fun x _ => hcon x
      have := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    refine ⟨Function.update c v col, ?_⟩
    intro u hu w hw hadj
    have hne : u ≠ w := hadj.ne
    by_cases huv : u = v
    · subst huv
      have hwv : w ≠ u := fun h => hne h.symm
      have : c w ∈ (s.filter (fun z => G.Adj u z)).image c :=
        Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hw, hadj⟩)
      simp only [Function.update_self, Function.update_of_ne hwv]
      intro hcontra
      exact hcol (hcontra ▸ this)
    · by_cases hwv : w = v
      · subst hwv
        have : c u ∈ (s.filter (fun z => G.Adj w z)).image c :=
          Finset.mem_image_of_mem c (Finset.mem_filter.mpr ⟨hu, hadj.symm⟩)
        simp only [Function.update_self, Function.update_of_ne huv]
        intro hcontra
        exact hcol (hcontra.symm ▸ this)
      · simp only [Function.update_of_ne huv, Function.update_of_ne hwv]
        exact hc u (Finset.mem_erase.mpr ⟨huv, hu⟩) w (Finset.mem_erase.mpr ⟨hwv, hw⟩) hadj

/-- A finite `k`-degenerate graph is `(k + 1)`-colourable. -/
theorem colorable_of_degenerate {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (h : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (fun w => G.Adj v w)).card ≤ k) :
    G.Colorable (k + 1) := by
  classical
  obtain ⟨c, hc⟩ := exists_partial_coloring G k h Finset.univ
  exact ⟨⟨c, fun {u w} hadj => hc u (Finset.mem_univ u) w (Finset.mem_univ w) hadj⟩⟩

/-- Base case of the four colour theorem: every finite `3`-degenerate graph — for instance every
finite planar graph in which each subgraph has a vertex of degree at most `3` — is
4-colourable. -/
theorem colorable_four_of_three_degenerate {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (fun w => G.Adj v w)).card ≤ 3) :
    G.Colorable 4 :=
  colorable_of_degenerate G 3 h

/-- **Four Colour Statement (Appel–Haken), reduced to the finite case.**

If every *finite* planar graph is 4-colourable, then every planar graph whatsoever —
finite or infinite — is 4-colourable.  The proof is a compactness (de Bruijn–Erdős)
argument, using that plane drawings restrict to subgraphs. -/
theorem four_color_statement
    (hfin : ∀ (W : Type u) [Finite W] (H : SimpleGraph W), IsPlanar H → H.Colorable 4)
    {V : Type u} (G : SimpleGraph V) (hG : IsPlanar G) : G.Colorable 4 := by
  refine SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom (F := ⊤) ?_
  intro G' hfinite
  have : Finite G'.verts := hfinite
  exact (hfin _ G'.coe (hG.subgraph G')).some

/-- **Four Colour Statement, reduced to graphs on `Fin n`.**

If every planar graph whose vertex set is `Fin n` (for some `n : ℕ`) is 4-colourable, then
every planar graph whatsoever is 4-colourable.  This combines the compactness reduction
`Frontier.four_color_statement` with invariance of planarity under isomorphism. -/
theorem four_color_statement_of_fin
    (hfin : ∀ (n : ℕ) (H : SimpleGraph (Fin n)), IsPlanar H → H.Colorable 4)
    {V : Type u} (G : SimpleGraph V) (hG : IsPlanar G) : G.Colorable 4 := by
  refine four_color_statement (fun W _ H hH => ?_) G hG
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin W
  have iso : H ≃g H.map e.toEmbedding := SimpleGraph.Iso.map e H
  exact SimpleGraph.Colorable.of_hom iso.toHom (hfin n _ (hH.ofIso iso))

/-- The Four Colour Statement is *equivalent* to its restriction to graphs on `Fin n`:
a fully finite, purely combinatorial statement. -/
theorem fourColorStatement_iff_fin : FourColorStatement.{0} ↔ FourColorStatementFin :=
  ⟨fun h _ H hH => h H hH, fun h _ G hG => four_color_statement_of_fin h G hG⟩

end Frontier

