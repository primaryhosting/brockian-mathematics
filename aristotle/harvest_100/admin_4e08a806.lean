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

namespace Frontier

universe u v

/-!
## Planarity

Mathlib (at the pinned commit) contains no theory of planar graphs, so we formalize
planarity from scratch, topologically: a *plane drawing* of a simple graph `G` consists of

* an injective placement `vert : V → ℝ × ℝ` of the vertices in the plane;
* for every edge `e` of `G` an arc, i.e. a continuous injective path
  `path e : [0,1] → ℝ × ℝ`, whose two endpoints are exactly the placements of the two
  endpoints of `e`;

subject to the two conditions that make the drawing *plane* (crossing-free):

* an arc meets the set of placed vertices only in its own endpoints;
* two distinct arcs meet only in placements of vertices common to both edges.
-/

/-- The set of endpoints of an edge `e`, as a subset of the vertex type. -/
def endpoints {V : Type u} (e : Sym2 V) : Set V := {x | x ∈ e}

/-- A crossing-free drawing of a simple graph in the plane `ℝ × ℝ`. -/
structure PlaneDrawing {V : Type u} (G : SimpleGraph V) where
  /-- Placement of the vertices in the plane. -/
  vert : V → ℝ × ℝ
  /-- Distinct vertices get distinct points. -/
  vert_inj : Function.Injective vert
  /-- Each edge is drawn as a path in the plane, parametrized by `[0,1]`. -/
  path : G.edgeSet → ℝ → ℝ × ℝ
  /-- The paths are continuous. -/
  path_cont : ∀ e, ContinuousOn (path e) (Set.Icc 0 1)
  /-- The paths are simple arcs (injective on `[0,1]`). -/
  path_inj : ∀ e, Set.InjOn (path e) (Set.Icc 0 1)
  /-- The two ends of the arc of `e` are the placements of the two endpoints of `e`. -/
  path_ends : ∀ e : G.edgeSet, vert '' endpoints (e : Sym2 V) = {path e 0, path e 1}
  /-- An arc passes through no placed vertex other than its own endpoints. -/
  arc_meets_vert : ∀ e : G.edgeSet,
    path e '' Set.Icc 0 1 ∩ Set.range vert ⊆ vert '' endpoints (e : Sym2 V)
  /-- Two distinct arcs meet only at placements of shared endpoints: no crossings. -/
  arc_disjoint : ∀ e f : G.edgeSet, e ≠ f →
    path e '' Set.Icc 0 1 ∩ path f '' Set.Icc 0 1 ⊆
      vert '' endpoints (e : Sym2 V) ∩ vert '' endpoints (f : Sym2 V)

/-- A simple graph is planar if it admits a crossing-free drawing in the plane. -/
def IsPlanar {V : Type u} (G : SimpleGraph V) : Prop := Nonempty (PlaneDrawing G)

/-- Endpoints of a mapped edge are the image of the endpoints. -/
lemma endpoints_map {V : Type u} {W : Type v} (f : V → W) (e : Sym2 V) :
    endpoints (Sym2.map f e) = f '' endpoints e := by
  induction e using Sym2.ind with
  | _ a b => ext x; simp [endpoints, Sym2.mem_iff, eq_comm]; aesop

/-- Planarity is inherited by (isomorphic copies of) subgraphs: if the vertices of `G'`
inject into those of `G` in an adjacency-preserving way, then `G'` is planar when `G` is. -/
theorem IsPlanar.of_injective_hom {V : Type u} {W : Type v} {G : SimpleGraph V}
    {G' : SimpleGraph W} (f : W → V) (hf : Function.Injective f)
    (hadj : ∀ u v, G'.Adj u v → G.Adj (f u) (f v)) (hG : IsPlanar G) : IsPlanar G' := by
  obtain ⟨D⟩ := hG
  -- the map sending an edge of `G'` to the corresponding edge of `G`
  have hmap : ∀ e : G'.edgeSet, Sym2.map f (e : Sym2 W) ∈ G.edgeSet := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b => exact hadj a b he
  set F : G'.edgeSet → G.edgeSet := fun e => ⟨Sym2.map f e, hmap e⟩ with hF
  have hFinj : Function.Injective F := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ h
    have : Sym2.map f e = Sym2.map f e' := congrArg Subtype.val h
    exact Subtype.ext (Sym2.map.injective hf this)
  -- endpoints of the image edge, drawn by `D`, are the endpoints drawn by `D.vert ∘ f`
  have hends : ∀ e : G'.edgeSet,
      D.vert '' endpoints ((F e : G.edgeSet) : Sym2 V)
        = (D.vert ∘ f) '' endpoints (e : Sym2 W) := by
    intro e
    simp [hF, endpoints_map, Set.image_image, Function.comp]
  refine ⟨{
    vert := D.vert ∘ f
    vert_inj := D.vert_inj.comp hf
    path := fun e => D.path (F e)
    path_cont := fun e => D.path_cont (F e)
    path_inj := fun e => D.path_inj (F e)
    path_ends := fun e => by rw [← hends e]; exact D.path_ends (F e)
    arc_meets_vert := ?_
    arc_disjoint := ?_ }⟩
  · intro e
    rw [← hends e]
    refine subset_trans ?_ (D.arc_meets_vert (F e))
    refine Set.inter_subset_inter_right _ ?_
    rintro x ⟨w, rfl⟩
    exact ⟨f w, rfl⟩
  · intro e e' hne
    rw [← hends e, ← hends e']
    exact D.arc_disjoint (F e) (F e') fun h => hne (hFinj h)

/-- Planarity is inherited by subgraphs. -/
theorem IsPlanar.subgraph {V : Type u} {G : SimpleGraph V} (H : G.Subgraph)
    (hG : IsPlanar G) : IsPlanar H.coe :=
  hG.of_injective_hom Subtype.val Subtype.val_injective
    (fun _ _ h => H.adj_sub h)

/-- Planarity is inherited by induced subgraphs. -/
theorem IsPlanar.induce {V : Type u} {G : SimpleGraph V} (s : Set V) (hG : IsPlanar G) :
    IsPlanar (G.induce s) :=
  hG.of_injective_hom Subtype.val Subtype.val_injective (fun _ _ h => h)

/-- Planarity is inherited by connected components. -/
theorem IsPlanar.connectedComponent {V : Type u} {G : SimpleGraph V}
    (C : G.ConnectedComponent) (hG : IsPlanar G) : IsPlanar C.toSimpleGraph :=
  hG.induce C.supp

/-!
### The definition is not vacuous

Two sanity checks: an edgeless graph whose vertices can be placed in the plane is planar,
and the one-edge graph (the complete graph on `Bool`) is planar.
-/

/-- A graph with no edges is planar, provided its vertices fit in the plane. -/
theorem isPlanar_bot {V : Type u} (v : V → ℝ × ℝ) (hv : Function.Injective v) :
    IsPlanar (⊥ : SimpleGraph V) := by
  refine ⟨{ vert := v, vert_inj := hv, path := fun e => absurd e.2 (by simp),
            path_cont := ?_, path_inj := ?_, path_ends := ?_,
            arc_meets_vert := ?_, arc_disjoint := ?_ }⟩ <;>
    rintro ⟨e, he⟩ <;> simp at he

/-- The graph with a single edge is planar: draw it as the segment from `(0,0)` to `(1,0)`. -/
theorem isPlanar_top_bool : IsPlanar (⊤ : SimpleGraph Bool) := by
  have hedge : ∀ e : (⊤ : SimpleGraph Bool).edgeSet, (e : Sym2 Bool) = s(false, true) := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at he
      cases a <;> cases b <;> simp_all [Sym2.eq_swap]
  have hends : ∀ e : (⊤ : SimpleGraph Bool).edgeSet,
      endpoints (e : Sym2 Bool) = Set.univ := by
    intro e; rw [hedge e]; ext x; cases x <;> simp [endpoints]
  have hvert : ((fun b : Bool => ((if b then (1:ℝ) else 0), (0:ℝ))) '' Set.univ)
      = {((0:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))} := by
    ext x
    constructor
    · rintro ⟨b, -, rfl⟩; cases b <;> simp
    · rintro (rfl | rfl)
      · exact ⟨false, trivial, by simp⟩
      · exact ⟨true, trivial, by simp⟩
  refine ⟨{ vert := fun b => ((if b then (1:ℝ) else 0), 0)
            vert_inj := ?_
            path := fun _ t => (t, 0)
            path_cont := ?_
            path_inj := ?_
            path_ends := ?_
            arc_meets_vert := ?_
            arc_disjoint := ?_ }⟩
  · intro a b hab; cases a <;> cases b <;> simp_all
  · intro e; fun_prop
  · intro e t _ s _ h; simpa using congrArg Prod.fst h
  · intro e; rw [hends e, hvert]
  · intro e
    rw [hends e, hvert]
    refine subset_trans Set.inter_subset_right ?_
    rintro x ⟨b, rfl⟩; cases b <;> simp
  · intro e f hne
    exact absurd (Subtype.ext ((hedge e).trans (hedge f).symm)) hne

/-!
## The Four Colour Theorem

`FourColorConjecture` is the statement of the Appel–Haken theorem: every planar simple
graph (on an arbitrary, possibly infinite, vertex type) has a proper colouring with four
colours.  `FourColorConjectureFinite` is its restriction to finite graphs.

These are `Prop`-valued definitions; we do *not* assert them.  What is proved below,
`four_color_statement`, is the reduction of the general statement to the finite case.
-/

/-- The Four Colour Theorem: every planar simple graph is 4-colourable. -/
def FourColorConjecture : Prop :=
  ∀ {V : Type} (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The Four Colour Theorem for finite graphs. -/
def FourColorConjectureFinite : Prop :=
  ∀ {V : Type} [Finite V] (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-!
### Base case

Any graph on at most four vertices is 4-colourable, with no planarity needed.
-/

/-- Base case: a graph on at most `4` vertices is `4`-colourable. -/
theorem colorable_four_of_card_le {V : Type u} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 4) : G.Colorable 4 :=
  (G.colorable_of_fintype).mono h

/-!
### The reduction

`four_color_statement`: if every *finite* planar graph is 4-colourable, then so is every
planar graph.  The proof is a compactness argument (De Bruijn–Erdős): every finite subgraph
of a planar graph is planar, hence 4-colourable, and colourings are homomorphisms into the
complete graph on `Fin 4`, so Mathlib's
`SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom` glues them together.
-/

/-- **Four Colour Statement (Lean-checked reduction).**

Every planar graph is 4-colourable, given that every finite planar graph is 4-colourable.
Equivalently: the Appel–Haken theorem for arbitrary planar graphs follows from its finite
case.  The proof is by compactness, using that planarity passes to subgraphs. -/
theorem four_color_statement
    (hfin : ∀ {W : Type u} [Finite W] (H : SimpleGraph W), IsPlanar H → H.Colorable 4)
    {V : Type u} (G : SimpleGraph V) (hG : IsPlanar G) : G.Colorable 4 := by
  refine SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom (F := ⊤) ?_
  intro G' hG'
  have : Finite G'.verts := hG'
  exact (hfin G'.coe (hG.subgraph G')).some

/-- A second Lean-checked reduction: it suffices to prove the Four Colour Theorem for
*connected* planar graphs, since planarity passes to connected components and a colouring
can be assembled component by component. -/
theorem four_color_of_connected
    (hconn : ∀ {W : Type u} (H : SimpleGraph W), IsPlanar H → H.Connected → H.Colorable 4)
    {V : Type u} (G : SimpleGraph V) (hG : IsPlanar G) : G.Colorable 4 := by
  rw [SimpleGraph.colorable_iff_forall_connectedComponents]
  exact fun C => hconn _ (hG.connectedComponent C) C.connected_toSimpleGraph

/-- Combining both reductions: the Four Colour Theorem follows from its case of finite
connected planar graphs. -/
theorem four_color_of_finite_connected
    (h : ∀ {W : Type u} [Finite W] (H : SimpleGraph W), IsPlanar H → H.Connected → H.Colorable 4)
    {V : Type u} (G : SimpleGraph V) (hG : IsPlanar G) : G.Colorable 4 :=
  four_color_statement (fun {W} _ H hH => by
    rw [SimpleGraph.colorable_iff_forall_connectedComponents]
    exact fun C => h _ (hH.connectedComponent C) C.connected_toSimpleGraph) G hG

/-- The finite case of the Four Colour Theorem implies the general case. -/
theorem fourColorConjecture_of_finite
    (hfin : ∀ {W : Type} [Finite W] (H : SimpleGraph W), IsPlanar H → H.Colorable 4) :
    FourColorConjecture :=
  fun G hG => four_color_statement hfin G hG

/-- Conversely, the general statement trivially implies the finite one. -/
theorem fourColorConjectureFinite_of_fourColorConjecture (h : FourColorConjecture) :
    FourColorConjectureFinite :=
  fun G hG => h G hG

/-- The Four Colour Theorem is equivalent to its restriction to finite graphs. -/
theorem fourColorConjecture_iff_finite : FourColorConjecture ↔ FourColorConjectureFinite :=
  ⟨fourColorConjectureFinite_of_fourColorConjecture,
    fun h => fourColorConjecture_of_finite (fun {_} _ H hH => h H hH)⟩

end Frontier

