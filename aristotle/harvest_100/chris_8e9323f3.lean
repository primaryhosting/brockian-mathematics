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

/-! ## Planarity

Mathlib has no theory of planar graphs, so we give a topological definition:
a graph is planar when its vertices can be placed at distinct points of the plane
and its edges drawn as simple arcs which meet only at common endpoints and pass
through no other vertex. -/

/-- `IsPlanarEmbedding G pos arc` says that `pos` places the vertices of `G` at
distinct points of the plane and `arc` draws each edge of `G` as a simple arc
between the images of its endpoints, so that arcs pass through no vertex other
than their endpoints and two distinct arcs meet only at common endpoints. -/
structure IsPlanarEmbedding {V : Type*} (G : SimpleGraph V) (pos : V → ℝ × ℝ)
    (arc : Sym2 V → Set (ℝ × ℝ)) : Prop where
  /-- distinct vertices are drawn at distinct points -/
  pos_injective : Function.Injective pos
  /-- each edge is drawn as a simple arc joining the images of its endpoints -/
  isArc : ∀ u v : V, G.Adj u v → ∃ γ : ℝ → ℝ × ℝ, ContinuousOn γ (Set.Icc 0 1) ∧
    Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = pos u ∧ γ 1 = pos v ∧
    arc s(u, v) = γ '' Set.Icc 0 1
  /-- an arc meets no vertex besides its own endpoints -/
  pos_mem_arc : ∀ u v w : V, G.Adj u v → pos w ∈ arc s(u, v) → w = u ∨ w = v
  /-- two distinct arcs meet only at images of common endpoints -/
  arc_inter : ∀ e f : Sym2 V, e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f →
    arc e ∩ arc f ⊆ pos '' {x : V | x ∈ e ∧ x ∈ f}

/-- A graph is *planar* if it admits a planar embedding, i.e. it can be drawn in the
plane with no crossing edges. -/
def Planar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (arc : Sym2 V → Set (ℝ × ℝ)), IsPlanarEmbedding G pos arc

/-- The four colour theorem (Appel–Haken), as a proposition: every planar graph is
4-colourable. -/
def FourColorTheorem : Prop :=
  ∀ {V : Type*} (G : SimpleGraph V), Planar G → G.Colorable 4

/-- The four colour theorem for finite graphs. -/
def FiniteFourColorTheorem : Prop :=
  ∀ {V : Type*} [Finite V] (G : SimpleGraph V), Planar G → G.Colorable 4

/-! ## Basic closure properties of planarity -/

/-- A subgraph (on the same vertex type) of a planar graph is planar. -/
theorem Planar.mono {V : Type*} {G G' : SimpleGraph V} (hle : G' ≤ G) (h : Planar G) :
    Planar G' := by
  classical
  obtain ⟨pos, arc, H⟩ := h
  refine ⟨pos, fun e => if e ∈ G'.edgeSet then arc e else ∅, ?_⟩
  constructor
  · exact H.pos_injective
  · intro u v huv
    obtain ⟨γ, hcont, hinj, h0, h1, hγ⟩ := H.isArc u v (hle huv)
    refine ⟨γ, hcont, hinj, h0, h1, ?_⟩
    rw [if_pos (show s(u, v) ∈ G'.edgeSet from huv)]
    exact hγ
  · intro u v w huv hw
    rw [if_pos (show s(u, v) ∈ G'.edgeSet from huv)] at hw
    exact H.pos_mem_arc u v w (hle huv) hw
  · intro e f he hf hef
    rw [if_pos he, if_pos hf]
    exact H.arc_inter e f (SimpleGraph.edgeSet_mono hle he) (SimpleGraph.edgeSet_mono hle hf) hef

/-- The subgraph induced on a set of vertices of a planar graph is planar. -/
theorem Planar.induce {V : Type*} {G : SimpleGraph V} (s : Set V) (h : Planar G) :
    Planar (G.induce s) := by
  obtain ⟨pos, arc, H⟩ := h
  refine ⟨fun x => pos (x : V), fun e => arc (Sym2.map Subtype.val e), ?_⟩
  constructor
  · exact fun a b hab => Subtype.ext (H.pos_injective hab)
  · intro u v huv
    obtain ⟨γ, hcont, hinj, h0, h1, hγ⟩ := H.isArc (u : V) (v : V) huv
    exact ⟨γ, hcont, hinj, h0, h1, by simpa using hγ⟩
  · intro u v w huv hw
    have hw' : pos (w : V) ∈ arc s((u : V), (v : V)) := by simpa using hw
    have := H.pos_mem_arc (u : V) (v : V) (w : V) huv hw'
    exact this.imp Subtype.ext Subtype.ext
  · intro e f he hf hef p hp
    have hef' : Sym2.map Subtype.val e ≠ Sym2.map Subtype.val f := fun hc =>
      hef (Sym2.map.injective Subtype.val_injective hc)
    have hemem : Sym2.map Subtype.val e ∈ G.edgeSet := by
      induction e using Sym2.ind with
      | _ a b => simpa using he
    have hfmem : Sym2.map Subtype.val f ∈ G.edgeSet := by
      induction f using Sym2.ind with
      | _ a b => simpa using hf
    obtain ⟨x, ⟨hx1, hx2⟩, hxp⟩ := H.arc_inter _ _ hemem hfmem hef' hp
    obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.mp hx1
    obtain ⟨z, hz, hzx⟩ := Sym2.mem_map.mp hx2
    have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
    exact ⟨y, ⟨hy, hyz ▸ hz⟩, by simpa [hyx] using hxp⟩

/-! ## Base case: small graphs -/

/-- Base case of the four colour theorem: any graph with at most four vertices
(in particular any planar one) is 4-colourable. -/
theorem colorable_four_of_card_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V ≤ 4) : G.Colorable 4 := by
  obtain ⟨f⟩ : Nonempty (V ↪ Fin 4) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hV)
  exact ⟨SimpleGraph.Coloring.mk f fun {u v} huv hc => G.ne_of_adj huv (f.injective hc)⟩

/-! ## Compactness: de Bruijn–Erdős -/

/-- **de Bruijn–Erdős**: a graph is `n`-colourable (`n ≠ 0`) as soon as each of its
finite induced subgraphs is. -/
theorem colorable_of_forall_finite_induce {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (hn : n ≠ 0) (h : ∀ s : Finset V, (G.induce (s : Set V)).Colorable n) :
    G.Colorable n := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  letI : TopologicalSpace (Fin n) := ⊥
  haveI : DiscreteTopology (Fin n) := ⟨rfl⟩
  set K : V × V → Set (V → Fin n) := fun p => {c | G.Adj p.1 p.2 → c p.1 ≠ c p.2} with hK
  have hclosed : ∀ p, IsClosed (K p) := by
    intro p
    by_cases hp : G.Adj p.1 p.2
    · have hEq : K p = (fun c : V → Fin n => (c p.1, c p.2)) ⁻¹' {q : Fin n × Fin n | q.1 ≠ q.2} := by
        ext c; simp [hK, hp]
      rw [hEq]
      exact (isClosed_discrete _).preimage (by fun_prop)
    · have hEq : K p = Set.univ := by ext c; simp [hK, hp]
      rw [hEq]; exact isClosed_univ
  have hne : (⋂ p, K p).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    obtain ⟨u, hu⟩ :=
      isCompact_univ.elim_finite_subfamily_closed K hclosed (by rw [Set.univ_inter, hempty])
    set t : Finset V := u.image Prod.fst ∪ u.image Prod.snd with ht
    obtain ⟨col⟩ := h t
    set c : V → Fin n := fun x =>
      if hx : x ∈ t then col ⟨x, Finset.mem_coe.mpr hx⟩ else Classical.arbitrary (Fin n) with hc
    have hmem : c ∈ Set.univ ∩ ⋂ p ∈ u, K p := by
      refine ⟨trivial, ?_⟩
      simp only [Set.mem_iInter]
      intro p hp hadj
      have h1 : p.1 ∈ t := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
      have h2 : p.2 ∈ t := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
      simp only [hc, dif_pos h1, dif_pos h2]
      exact col.valid (show (G.induce (t : Set V)).Adj ⟨p.1, _⟩ ⟨p.2, _⟩ from hadj)
    rw [hu] at hmem
    exact hmem
  obtain ⟨c, hcmem⟩ := hne
  exact ⟨SimpleGraph.Coloring.mk c fun {u v} huv => (Set.mem_iInter.mp hcmem (u, v)) huv⟩

/-! ## The reduction -/

/-- **Lean-checked reduction of the four colour statement to the finite case**:
if every finite planar graph is 4-colourable, then every planar graph is
4-colourable. -/
theorem four_color_statement.{u} : FiniteFourColorTheorem.{u} → FourColorTheorem.{u} := by
  intro hfin V G hG
  refine colorable_of_forall_finite_induce G (by norm_num) fun s => ?_
  exact hfin _ (hG.induce (s : Set V))

end Frontier

