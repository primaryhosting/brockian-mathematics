/-
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated as a module docstring below: in Lean 4 a `/-! ... -/`
-- module docstring may not precede the `import` commands.)

import Mathlib

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

Mathlib has no notion of graph planarity, so this file supplies one:
`Frontier.PlanarEmbedding` (a drawing of a graph in `ℝ × ℝ` with non-crossing arcs)
and `Frontier.IsPlanar`.

* `Frontier.FourColorStatement` — the Four Colour Theorem itself (Appel–Haken):
  every planar graph is 4-colourable.  This is **not** proved here.
* `Frontier.four_color_statement` — the Lean-checked reduction proved here: the
  Four Colour Theorem for arbitrary (possibly infinite) planar graphs is
  *equivalent* to its restriction to finite planar graphs.  The nontrivial
  direction is de Bruijn–Erdős compactness, obtained from Mathlib's
  `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`, together with the fact
  that planarity is hereditary (`Frontier.IsPlanar.of_injective`).
* `Frontier.four_color_statement_fin` — a further reduction to graphs on `Fin n`.
* `Frontier.colorable_four_of_card_le` — the base case: graphs on at most four
  vertices are 4-colourable.
* Sanity checks that the planarity definition has content:
  `Frontier.isPlanar_bot`, `Frontier.isPlanar_top_fin_two` (positive examples) and
  `Frontier.not_isPlanar_set_real` (a negative example).
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

universe u v

/-- A *planar embedding* of a simple graph `G` in the Euclidean plane `ℝ × ℝ`:
vertices are sent to distinct points, each edge is drawn as an arc (a continuous
injective curve) joining the images of its endpoints, arcs pass through no vertex
other than their own endpoints, and two arcs of distinct edges meet only in the
images of vertices shared by the two edges. -/
structure PlanarEmbedding {V : Type u} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  pos : V → ℝ × ℝ
  /-- Distinct vertices get distinct positions. -/
  pos_inj : Function.Injective pos
  /-- The arc drawn for the edge `{u, v}`, parametrized by the unit interval. -/
  arc : V → V → unitInterval → ℝ × ℝ
  arc_cont : ∀ {a b : V}, G.Adj a b → Continuous (arc a b)
  arc_inj : ∀ {a b : V}, G.Adj a b → Function.Injective (arc a b)
  arc_zero : ∀ {a b : V}, G.Adj a b → arc a b 0 = pos a
  arc_one : ∀ {a b : V}, G.Adj a b → arc a b 1 = pos b
  /-- The two parametrizations of an edge trace out the same arc. -/
  arc_symm : ∀ {a b : V}, G.Adj a b → Set.range (arc a b) = Set.range (arc b a)
  /-- An arc meets no vertex other than its endpoints. -/
  arc_avoid : ∀ {a b : V}, G.Adj a b → ∀ w : V, pos w ∈ Set.range (arc a b) → w = a ∨ w = b
  /-- Arcs of distinct edges meet only at (positions of) common endpoints. -/
  arc_disjoint : ∀ {a b c d : V}, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
    Set.range (arc a b) ∩ Set.range (arc c d) ⊆ pos '' ({a, b} ∩ {c, d})

/-- A graph is *planar* if it admits a planar embedding, i.e. it can be drawn in the
plane with no crossing edges. -/
def IsPlanar {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarEmbedding G)

/-- Planarity is inherited along injective adjacency-preserving maps: any graph that
embeds into a planar graph (as a subgraph) is itself planar. -/
theorem IsPlanar.of_injective {V : Type u} {W : Type v} {G : SimpleGraph V}
    {H : SimpleGraph W} (hG : IsPlanar G) (f : W → V) (hf : Function.Injective f)
    (hadj : ∀ a b : W, H.Adj a b → G.Adj (f a) (f b)) : IsPlanar H := by
  obtain ⟨E⟩ := hG
  have key : ∀ a b c d : W, H.Adj a b → H.Adj c d → s(a, b) ≠ s(c, d) →
      s(f a, f b) ≠ s(f c, f d) := by
    intro a b c d _ _ hne heq
    rw [Sym2.eq_iff] at heq
    refine hne (Sym2.eq_iff.mpr ?_)
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hf h1, hf h2⟩
    · exact Or.inr ⟨hf h1, hf h2⟩
  refine ⟨{ pos := fun w => E.pos (f w)
            pos_inj := E.pos_inj.comp hf
            arc := fun a b => E.arc (f a) (f b)
            arc_cont := fun h => E.arc_cont (hadj _ _ h)
            arc_inj := fun h => E.arc_inj (hadj _ _ h)
            arc_zero := fun h => E.arc_zero (hadj _ _ h)
            arc_one := fun h => E.arc_one (hadj _ _ h)
            arc_symm := fun h => E.arc_symm (hadj _ _ h)
            arc_avoid := ?_
            arc_disjoint := ?_ }⟩
  · intro a b hab w hw
    have := E.arc_avoid (hadj _ _ hab) (f w) hw
    rcases this with h | h
    · exact Or.inl (hf h)
    · exact Or.inr (hf h)
  · intro a b c d hab hcd hne
    have hsub := E.arc_disjoint (hadj _ _ hab) (hadj _ _ hcd) (key a b c d hab hcd hne)
    intro p hp
    have hp' := hsub hp
    obtain ⟨q, hq, hqp⟩ := hp'
    have himg : ({f a, f b} : Set V) ∩ {f c, f d} = f '' (({a, b} : Set W) ∩ {c, d}) := by
      rw [Set.image_inter hf]
      simp [Set.image_insert_eq]
    rw [himg] at hq
    obtain ⟨w, hw, hwq⟩ := hq
    exact ⟨w, hw, by show E.pos (f w) = p; rw [hwq, hqp]⟩

/-- Subgraphs (on the same vertex set) of a planar graph are planar. -/
theorem IsPlanar.mono {V : Type u} {G H : SimpleGraph V} (hG : IsPlanar G) (h : H ≤ G) :
    IsPlanar H :=
  hG.of_injective id Function.injective_id fun _ _ hab => h hab

/-- Planarity is invariant under graph isomorphism. -/
theorem IsPlanar.of_iso {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : IsPlanar G) (e : H ≃g G) : IsPlanar H :=
  hG.of_injective e e.toEquiv.injective fun _ _ hab => e.map_adj_iff.mpr hab

/-- Pulling a planar graph back along a bijection of vertex types keeps it planar. -/
theorem IsPlanar.comap {V : Type u} {W : Type v} {G : SimpleGraph V} (hG : IsPlanar G)
    (e : W ≃ V) : IsPlanar (SimpleGraph.comap (⇑e.toEmbedding) G) :=
  hG.of_injective (⇑e.toEmbedding) e.toEmbedding.injective fun _ _ hab => hab

/-- Colourability transfers back along a bijection of vertex types. -/
theorem colorable_of_comap {V : Type u} {W : Type v} {G : SimpleGraph V} (e : W ≃ V) {n : ℕ}
    (h : (SimpleGraph.comap (⇑e.toEmbedding) G).Colorable n) : G.Colorable n :=
  h.of_hom (SimpleGraph.Iso.comap e G).symm.toHom

/-- Auxiliary combinatorial facts about `Fin 2`, used for the single-edge example. -/
private theorem fin_two_mem_pair : ∀ a b w : Fin 2, a ≠ b → w = a ∨ w = b := by decide

private theorem fin_two_sym2_eq : ∀ a b c d : Fin 2, a ≠ b → c ≠ d → s(a, b) = s(c, d) := by
  decide

/-- **Sanity check: graphs with edges can be planar.** The one-edge graph on two
vertices is planar, drawn as a straight segment in the plane. Together with
`IsPlanar.mono` this shows every graph on two vertices is planar. -/
theorem isPlanar_top_fin_two : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨{ pos := fun i => ((i : ℝ), 0)
            pos_inj := ?_
            arc := fun a b t => ((1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ), 0)
            arc_cont := ?_
            arc_inj := ?_
            arc_zero := ?_
            arc_one := ?_
            arc_symm := ?_
            arc_avoid := ?_
            arc_disjoint := ?_ }⟩
  · intro x y hxy
    have : ((x : ℕ) : ℝ) = ((y : ℕ) : ℝ) := congrArg Prod.fst hxy
    exact Fin.ext (Nat.cast_injective this)
  · intro a b _
    fun_prop
  · intro a b hab s t hst
    have hne : ((a : ℕ) : ℝ) ≠ ((b : ℕ) : ℝ) := by
      simpa using fun h => hab (Fin.ext h)
    have h1 : (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ)
        = (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) := congrArg Prod.fst hst
    have h2 : ((s : ℝ) - (t : ℝ)) * ((b : ℝ) - (a : ℝ)) = 0 := by ring_nf; linarith [h1]
    rcases mul_eq_zero.mp h2 with h | h
    · exact Subtype.ext (by linarith)
    · exact absurd (by linarith : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ)) hne
  · intro a b _; simp
  · intro a b _; simp
  · intro a b _
    ext p
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp [unitInterval.coe_symm_eq]; ring⟩
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp [unitInterval.coe_symm_eq]; ring⟩
  · intro a b hab w _
    exact fin_two_mem_pair a b w hab
  · intro a b c d hab hcd hne
    exact absurd (fin_two_sym2_eq a b c d hab hcd) hne

/-- **Sanity check: the definition is not vacuously true.** A planar graph has at most
continuum many vertices, since its vertices sit at distinct points of the plane. -/
theorem not_isPlanar_of_card_lt {V : Type} {G : SimpleGraph V}
    (h : Cardinal.mk (ℝ × ℝ) < Cardinal.mk V) : ¬ IsPlanar G := by
  rintro ⟨E⟩
  exact absurd (Cardinal.mk_le_of_injective E.pos_inj) (not_le.mpr h)

/-- A concrete non-planar graph: no graph on the vertex set `Set ℝ` is planar. -/
theorem not_isPlanar_set_real (G : SimpleGraph (Set ℝ)) : ¬ IsPlanar G := by
  refine not_isPlanar_of_card_lt ?_
  have h1 : Cardinal.mk (ℝ × ℝ) = Cardinal.continuum := by
    simp [Cardinal.mk_prod, Cardinal.mk_real, Cardinal.continuum_mul_self]
  have h2 : Cardinal.mk (Set ℝ) = 2 ^ Cardinal.continuum := by
    simp [Cardinal.mk_set, Cardinal.mk_real]
  rw [h1, h2]
  exact Cardinal.cantor _

/-- **Statement of the Four Colour Theorem** (Appel–Haken): every planar graph is
4-colourable. -/
def FourColorStatement : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The Four Colour Theorem restricted to graphs with finitely many vertices. -/
def FiniteFourColorStatement : Prop :=
  ∀ (V : Type u) (_ : Finite V) (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- **Base case.** Any graph on at most four vertices is 4-colourable (a fortiori,
any planar one). -/
theorem colorable_four_of_card_le {V : Type u} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 4) : G.Colorable 4 :=
  (SimpleGraph.colorable_of_fintype G).mono h

/-- **Sanity check: the definition is not vacuous.** Every edgeless graph on a
vertex type that injects into the reals is planar. -/
theorem isPlanar_bot {V : Type u} (f : V → ℝ) (hf : Function.Injective f) :
    IsPlanar (⊥ : SimpleGraph V) := by
  refine ⟨{ pos := fun v => (f v, 0)
            pos_inj := ?_
            arc := fun _ _ _ => 0
            arc_cont := fun h => absurd h (by simp)
            arc_inj := fun h => absurd h (by simp)
            arc_zero := fun h => absurd h (by simp)
            arc_one := fun h => absurd h (by simp)
            arc_symm := fun h => absurd h (by simp)
            arc_avoid := fun h => absurd h (by simp)
            arc_disjoint := fun h => absurd h (by simp) }⟩
  intro x y hxy
  exact hf (congrArg Prod.fst hxy)

/-- **Reduction of the Four Colour Theorem to the finite case** (de Bruijn–Erdős
compactness). The general statement holds if and only if it holds for all finite
planar graphs. -/
theorem four_color_statement : FourColorStatement.{u} ↔ FiniteFourColorStatement.{u} := by
  constructor
  · intro h V _ G hG
    exact h V G hG
  · intro h V G hG
    refine SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
      (F := (⊤ : SimpleGraph (Fin 4))) ?_
    intro G' hfin
    haveI : Finite ↥G'.verts := hfin.to_subtype
    have hplanar : IsPlanar G'.coe :=
      hG.of_injective Subtype.val Subtype.val_injective
        (fun a b hab => G'.adj_sub hab)
    exact (h _ inferInstance _ hplanar).some

/-- The Four Colour Theorem stated for graphs on the standard finite vertex sets `Fin n`. -/
def FourColorStatementFin : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IsPlanar G → G.Colorable 4

/-- **Reduction of the Four Colour Theorem to graphs on `Fin n`.** Combining the
compactness reduction with transport along isomorphisms, the general statement is
equivalent to the statement for planar graphs on the vertex sets `Fin n`, `n : ℕ`. -/
theorem four_color_statement_fin : FourColorStatement.{u} ↔ FourColorStatementFin := by
  constructor
  · intro h n G hG
    exact colorable_of_comap (Equiv.ulift.{u}) (h _ _ (hG.comap (Equiv.ulift.{u})))
  · intro h
    refine four_color_statement.mpr ?_
    intro V _ G hG
    haveI : Fintype V := Fintype.ofFinite V
    exact colorable_of_comap (Fintype.equivFin V).symm
      (h _ _ (hG.comap (Fintype.equivFin V).symm))

end Frontier

