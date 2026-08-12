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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Overview

The Four Colour Theorem (Appel–Haken) states that every planar graph can be properly
coloured with four colours.  Its only known proofs rely on a massive computer-assisted
case analysis, so the theorem itself is not proved here.  What this file contains is:

* a formalisation of the notion of a *planar graph*, via crossing-free drawings in the
  plane (`Frontier.PlanarEmbedding`, `Frontier.IsPlanar`);
* the formal statement of the Four Colour Theorem (`Frontier.FourColorConjecture`);
* structural facts about planarity: it is inherited by subgraphs
  (`Frontier.IsPlanar.mono`, `Frontier.IsPlanar.comap`, `Frontier.IsPlanar.induce`);
* examples showing the notion is not vacuous (`Frontier.isPlanar_bot_fin`,
  `Frontier.isPlanar_top_fin_two`);
* base cases which are unconditionally proved
  (`Frontier.colorable_four_of_card_le`, `Frontier.colorable_four_of_bot`);
* and, as the main target, a **Lean-checked reduction**
  (`Frontier.four_color_statement`): the Four Colour Theorem for arbitrary planar graphs
  follows from — and is therefore equivalent to — the Four Colour Theorem for *finite,
  connected* planar graphs *of minimum degree at least four*.  The reduction to the
  finite case is a de Bruijn–Erdős style compactness argument; the reduction to the
  connected case is the decomposition of a graph into its connected components; and the
  reduction to minimum degree four is the classical minimal-counterexample argument
  which deletes a vertex with at most three neighbours.  Weaker intermediate forms are
  also recorded (`Frontier.four_color_statement_finite`,
  `Frontier.four_color_statement_finite_connected`).
-/

namespace Frontier

/-! ## Planar graphs -/

/-- A *plane drawing* (planar embedding) of a simple graph `G`:

* every vertex `v` is sent to a point `pt v` of the plane, injectively;
* every edge `uv` is drawn as an arc `arc u v`, i.e. the image of a continuous injective
  map defined on `[0,1]`, whose endpoints are `pt u` and `pt v`;
* two distinct edges meet only in the images of their common endpoints;
* no arc passes through the point of a vertex which is not one of its endpoints.

This is the standard notion of a drawing of a graph in the plane without crossings. -/
structure PlanarEmbedding {V : Type*} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  pt : V → ℝ × ℝ
  /-- Distinct vertices get distinct points. -/
  pt_inj : Function.Injective pt
  /-- The set of points of the plane covered by the arc drawing the edge `uv`. -/
  arc : V → V → Set (ℝ × ℝ)
  /-- The arc drawing `uv` is the arc drawing `vu`. -/
  arc_symm : ∀ u v, arc u v = arc v u
  /-- The arc drawing an edge really is an arc from one endpoint to the other. -/
  arc_isArc : ∀ {u v : V}, G.Adj u v → ∃ g : ℝ → ℝ × ℝ,
    ContinuousOn g (Set.Icc 0 1) ∧ Set.InjOn g (Set.Icc 0 1) ∧
      g 0 = pt u ∧ g 1 = pt v ∧ arc u v = g '' Set.Icc 0 1
  /-- Two distinct edges meet only at points coming from common endpoints. -/
  arc_inter : ∀ {u v x y : V}, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
    arc u v ∩ arc x y ⊆ pt '' ({u, v} ∩ {x, y})
  /-- An arc avoids the points of all vertices other than its endpoints. -/
  pt_notMem : ∀ {u v w : V}, G.Adj u v → w ≠ u → w ≠ v → pt w ∉ arc u v

/-- A graph is *planar* when it admits a drawing in the plane without crossings. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop := Nonempty (PlanarEmbedding G)

/-- The edgeless graph on `Fin n` is planar: place the vertices on a line. -/
theorem isPlanar_bot_fin (n : ℕ) : IsPlanar (⊥ : SimpleGraph (Fin n)) :=
  ⟨{ pt := fun i => ((i : ℕ), 0)
     pt_inj := by
       intro i j hij
       have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := congrArg Prod.fst hij
       exact Fin.ext (Nat.cast_injective this)
     arc := fun _ _ => ∅
     arc_symm := fun _ _ => rfl
     arc_isArc := fun h => absurd h (by simp)
     arc_inter := fun h => absurd h (by simp)
     pt_notMem := fun h => absurd h (by simp) }⟩

/-- A single edge is planar: draw it as the horizontal unit segment.  Together with
`Frontier.isPlanar_bot_fin` this shows that the notion of planarity defined above is not
vacuous, i.e. that graphs with edges can indeed be drawn. -/
theorem isPlanar_top_fin_two : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨{ pt := fun i => ((i : ℕ), 0)
            pt_inj := ?_
            arc := fun _ _ => (fun t : ℝ => (t, (0:ℝ))) '' Set.Icc 0 1
            arc_symm := fun _ _ => rfl
            arc_isArc := ?_
            arc_inter := ?_
            pt_notMem := ?_ }⟩
  · intro i j hij
    have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := congrArg Prod.fst hij
    exact Fin.ext (Nat.cast_injective this)
  · intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all
    · refine ⟨fun t : ℝ => (t, (0:ℝ)), by fun_prop,
        (fun a _ b _ hab => congrArg Prod.fst hab), ?_, ?_, rfl⟩ <;> norm_num
    · refine ⟨fun t : ℝ => (1 - t, (0:ℝ)), by fun_prop, ?_, ?_, ?_, ?_⟩
      · intro a _ b _ hab
        have := congrArg Prod.fst hab
        simp only at this
        linarith
      · norm_num
      · norm_num
      · ext ⟨a, b⟩
        simp only [Set.mem_image, Set.mem_Icc, Prod.mk.injEq]
        constructor
        · rintro ⟨t, ⟨ht0, ht1⟩, h1, h2⟩
          exact ⟨1 - t, ⟨by linarith, by linarith⟩, by linarith, h2⟩
        · rintro ⟨t, ⟨ht0, ht1⟩, h1, h2⟩
          exact ⟨1 - t, ⟨by linarith, by linarith⟩, h1, h2⟩
  · intro u v x y huv hxy hne
    exfalso
    apply hne
    fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;> simp_all
  · intro u v w huv hwu hwv
    exfalso
    fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all

/-! ## Planarity is hereditary -/

/-- Planarity is preserved by deleting edges. -/
theorem IsPlanar.mono {V : Type*} {G H : SimpleGraph V} (hle : H ≤ G) (hG : IsPlanar G) :
    IsPlanar H := by
  obtain ⟨e⟩ := hG
  exact ⟨{ pt := e.pt, pt_inj := e.pt_inj, arc := e.arc, arc_symm := e.arc_symm,
           arc_isArc := fun h => e.arc_isArc (hle h),
           arc_inter := fun h1 h2 hne => e.arc_inter (hle h1) (hle h2) hne,
           pt_notMem := fun h h1 h2 => e.pt_notMem (hle h) h1 h2 }⟩

/-- Planarity is preserved by passing to the subgraph induced along an injection of vertex
sets: restricting a drawing of `G` to the image of `f` is a drawing of `G.comap f`. -/
theorem IsPlanar.comap {V W : Type*} {G : SimpleGraph V} (f : W → V) (hf : Function.Injective f)
    (hG : IsPlanar G) : IsPlanar (G.comap f) := by
  obtain ⟨e⟩ := hG
  refine ⟨{ pt := fun w => e.pt (f w), pt_inj := e.pt_inj.comp hf,
            arc := fun a b => e.arc (f a) (f b),
            arc_symm := fun a b => e.arc_symm _ _,
            arc_isArc := fun h => e.arc_isArc h, arc_inter := ?_,
            pt_notMem := fun h h1 h2 =>
              e.pt_notMem h (fun hc => h1 (hf hc)) (fun hc => h2 (hf hc)) }⟩
  intro u v x y h1 h2 hne p hp
  have hne' : s(f u, f v) ≠ s(f x, f y) := by
    intro hEq
    apply hne
    rw [Sym2.eq_iff] at hEq ⊢
    rcases hEq with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨hf h3, hf h4⟩
    · exact Or.inr ⟨hf h3, hf h4⟩
  obtain ⟨w, hw, hwp⟩ := e.arc_inter h1 h2 hne' hp
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  obtain ⟨hw1, hw2⟩ := hw
  rcases hw1 with h | h <;> rcases hw2 with h' | h'
  · exact ⟨u, ⟨by simp, by simp [hf (h.symm.trans h')]⟩, by simpa only [← h] using hwp⟩
  · exact ⟨u, ⟨by simp, by simp [hf (h.symm.trans h')]⟩, by simpa only [← h] using hwp⟩
  · exact ⟨v, ⟨by simp, by simp [hf (h.symm.trans h')]⟩, by simpa only [← h] using hwp⟩
  · exact ⟨v, ⟨by simp, by simp [hf (h.symm.trans h')]⟩, by simpa only [← h] using hwp⟩

/-- Every graph on two vertices is planar. -/
theorem isPlanar_of_fin_two (G : SimpleGraph (Fin 2)) : IsPlanar G :=
  IsPlanar.mono le_top isPlanar_top_fin_two

/-- Planarity is preserved by passing to an induced subgraph. -/
theorem IsPlanar.induce {V : Type*} {G : SimpleGraph V} (s : Set V) (hG : IsPlanar G) :
    IsPlanar (G.induce s) :=
  IsPlanar.comap _ Subtype.val_injective hG

/-- Planarity is preserved by passing to the subgraph induced on a connected component. -/
theorem IsPlanar.connectedComponent {V : Type*} {G : SimpleGraph V} (hG : IsPlanar G)
    (c : G.ConnectedComponent) : IsPlanar c.toSimpleGraph :=
  hG.induce c.supp

/-! ## The statement of the Four Colour Theorem, and weakened forms of it -/

/-- **The statement of the Four Colour Theorem** (Appel–Haken): every planar graph admits a
proper colouring with four colours. -/
def FourColorConjecture : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The Four Colour Theorem restricted to graphs with finitely many vertices. -/
def FourColorConjectureFinite : Prop :=
  ∀ (V : Type) (_ : Finite V) (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The Four Colour Theorem restricted to finite *connected* graphs. -/
def FourColorConjectureFiniteConnected : Prop :=
  ∀ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.Connected → IsPlanar G → G.Colorable 4

/-- The Four Colour Theorem restricted to finite connected graphs of minimum degree at
least four: the *reduced form* of the conjecture. -/
def FourColorConjectureReduced : Prop :=
  ∀ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.Connected → IsPlanar G →
    (∀ v : V, 4 ≤ (G.neighborSet v).ncard) → G.Colorable 4

/-! ## Base cases -/

/-- Base case: any graph on at most four vertices is four-colourable. -/
theorem colorable_four_of_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 4) : G.Colorable 4 :=
  (SimpleGraph.colorable_of_fintype G).mono h

/-- Base case: the edgeless graph is four-colourable. -/
theorem colorable_four_of_bot (V : Type*) : (⊥ : SimpleGraph V).Colorable 4 :=
  ⟨SimpleGraph.Coloring.mk (fun _ => 0) (by simp)⟩

/-! ## The reduction -/

/-- Reduction to the connected case: if every connected planar graph is four-colourable,
then so is every planar graph.  (Colour each connected component separately.) -/
theorem fourColorConjecture_of_connected
    (h : ∀ (V : Type) (G : SimpleGraph V), G.Connected → IsPlanar G → G.Colorable 4) :
    FourColorConjecture := by
  intro V G hG
  rw [SimpleGraph.colorable_iff_forall_connectedComponents]
  intro c
  exact h _ _ c.connected_toSimpleGraph (hG.connectedComponent c)

/-- Reduction of the finite case to the finite connected case. -/
theorem fourColorConjectureFinite_of_finiteConnected
    (h : FourColorConjectureFiniteConnected) : FourColorConjectureFinite := by
  intro V hV G hG
  rw [SimpleGraph.colorable_iff_forall_connectedComponents]
  intro c
  exact h _ (Subtype.finite) _ c.connected_toSimpleGraph (hG.connectedComponent c)

/-- Reduction to the finite case (a de Bruijn–Erdős style compactness argument): if every
finite planar graph is four-colourable, then so is every planar graph. -/
theorem fourColorConjecture_of_finite (h : FourColorConjectureFinite) : FourColorConjecture := by
  intro V G hG
  have key : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe →g (⊤ : SimpleGraph (Fin 4)) := by
    intro G' hfin
    haveI : Finite ↥G'.verts := hfin
    have hle : G'.coe ≤ SimpleGraph.comap (Subtype.val) G := fun _ _ hab => G'.adj_sub hab
    exact (h _ ‹Finite ↥G'.verts› _
      (IsPlanar.mono hle (IsPlanar.comap Subtype.val Subtype.val_injective hG))).some
  exact SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom key

/-- Intermediate form of the reduction: the Four Colour Theorem is equivalent to the Four
Colour Theorem for finite planar graphs. -/
theorem four_color_statement_finite : FourColorConjectureFinite ↔ FourColorConjecture :=
  ⟨fourColorConjecture_of_finite, fun h V _ G hG => h V G hG⟩

/-- Intermediate form of the reduction: the Four Colour Theorem is equivalent to the Four
Colour Theorem for finite connected planar graphs. -/
theorem four_color_statement_finite_connected :
    FourColorConjectureFiniteConnected ↔ FourColorConjecture :=
  ⟨fun h => fourColorConjecture_of_finite (fourColorConjectureFinite_of_finiteConnected h),
    fun h V _ G _ hG => h V G hG⟩

/-- The heart of the reduction to minimum degree four: by induction on the number of
vertices, a vertex with at most three neighbours can be deleted, four-coloured by the
induction hypothesis, and the deleted vertex given a colour missing from its neighbours;
a disconnected graph is handled component by component. -/
private theorem colorable_four_of_reduced_aux (h : FourColorConjectureReduced) :
    ∀ (n : ℕ) (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = n → IsPlanar G → G.Colorable 4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V hV G hcard hG
    classical
    by_cases hd : ∀ v : V, 4 ≤ (G.neighborSet v).ncard
    · by_cases hconn : G.Connected
      · exact h V (Finite.of_fintype V) G hconn hG hd
      · rcases isEmpty_or_nonempty V with hem | hne
        · exact SimpleGraph.Colorable.of_isEmpty 4
        · have hex : ∃ u w : V, ¬ G.Reachable u w := by
            by_contra hcon
            push_neg at hcon
            exact hconn { preconnected := hcon, nonempty := hne }
          obtain ⟨u, w, huw⟩ := hex
          rw [SimpleGraph.colorable_iff_forall_connectedComponents]
          intro c
          have hx : ∃ x : V, x ∉ c.supp := by
            by_contra hcon
            push_neg at hcon
            exact huw (c.reachable_of_mem_supp (hcon u) (hcon w))
          obtain ⟨x, hx⟩ := hx
          have hlt : Fintype.card ↥c.supp < n := by
            rw [← hcard]
            refine Fintype.card_lt_of_injective_not_surjective (fun y : ↥c.supp => (y : V))
              Subtype.val_injective ?_
            intro hsurj
            obtain ⟨y, hy⟩ := hsurj x
            exact hx (hy ▸ y.2)
          exact ih _ hlt _ _ _ rfl (hG.connectedComponent c)
    · push_neg at hd
      obtain ⟨v, hv⟩ := hd
      have hcardW : Fintype.card {w : V // w ≠ v} < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (p := fun w : V => w ≠ v) (x := v) (by simp)
      obtain ⟨C'⟩ := ih (Fintype.card {w : V // w ≠ v}) hcardW {w : V // w ≠ v} inferInstance
        (G.comap Subtype.val) rfl (IsPlanar.comap _ Subtype.val_injective hG)
      set c' : V → Fin 4 := fun w => if hw : w = v then 0 else C' ⟨w, hw⟩ with hc'
      set T : Set (Fin 4) := c' '' (G.neighborSet v) with hT
      have hTcard : T.ncard < 4 := lt_of_le_of_lt (Set.ncard_image_le (Set.toFinite _)) hv
      have hex : ∃ a : Fin 4, a ∉ T := by
        by_contra hcon
        push_neg at hcon
        have huniv : T = Set.univ := Set.eq_univ_of_forall hcon
        rw [huniv, Set.ncard_univ] at hTcard
        simp at hTcard
      obtain ⟨a, ha⟩ := hex
      refine ⟨SimpleGraph.Coloring.mk (fun w => if w = v then a else c' w) ?_⟩
      intro x y hxy
      by_cases hxv : x = v
      · subst hxv
        have hyv : y ≠ x := (G.ne_of_adj hxy).symm
        simp only [if_neg hyv]
        intro hcon
        exact ha ⟨y, hxy, hcon.symm⟩
      · by_cases hyv : y = v
        · subst hyv
          simp only [if_neg hxv]
          intro hcon
          exact ha ⟨x, hxy.symm, hcon⟩
        · simp only [if_neg hxv, if_neg hyv, hc', dif_neg hxv, dif_neg hyv]
          exact C'.valid hxy

/-- Reduction of the finite case to finite connected planar graphs of minimum degree at
least four. -/
theorem fourColorConjectureFinite_of_reduced (h : FourColorConjectureReduced) :
    FourColorConjectureFinite := by
  intro V hV G hG
  haveI := Fintype.ofFinite V
  exact colorable_four_of_reduced_aux h (Fintype.card V) V inferInstance G rfl hG

/-- **Lean-checked reduction of the Four Colour Theorem.**

The Four Colour Theorem — *every planar graph is four-colourable* — is equivalent to its
restriction to *finite connected* planar graphs *in which every vertex has at least four
neighbours*.

The nontrivial implication combines three reductions.  The passage from arbitrary graphs
to finite graphs is a compactness (de Bruijn–Erdős) argument, using that planarity is
inherited by subgraphs.  The passage to connected graphs is the decomposition of a graph
into its connected components, using that planarity is inherited by induced subgraphs.
The passage to minimum degree four is the classical minimal-counterexample argument: a
vertex with at most three neighbours may be deleted and re-coloured at the end, since it
leaves one of the four colours free. -/
theorem four_color_statement : FourColorConjectureReduced ↔ FourColorConjecture :=
  ⟨fun h => fourColorConjecture_of_finite (fourColorConjectureFinite_of_reduced h),
    fun h V _ G _ hG _ => h V G hG⟩

end Frontier

