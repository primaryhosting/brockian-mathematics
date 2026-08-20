import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON FILE LAYOUT: Lean 4 requires `import` commands to come first in a file, so the
mandated header block appears immediately after the single `import Mathlib` line, with its
text reproduced verbatim.
-/

namespace Chem

open SimpleGraph

section TreeCotree

variable {α : Type*} {G H : SimpleGraph α}

/-- The edges of a subgraph `H ≤ G`, viewed inside the edge set of `G`, biject with the
edges of `H`. -/
def edgeSubtypeEquiv (h : H ≤ G) :
    {e : G.edgeSet // (e : Sym2 α) ∈ H.edgeSet} ≃ H.edgeSet where
  toFun e := ⟨(e.1 : Sym2 α), e.2⟩
  invFun e := ⟨⟨(e : Sym2 α), edgeSet_mono h e.2⟩, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TreeCotree

/-- **Euler's polyhedron formula**, `V - E + F = 2`, in the form `V + F = E + 2`.

The combinatorial data of (the surface of) a convex polyhedron — say a fullerene cage — is:

* a finite vertex set `Vertex` and the `skeleton` graph on it (the 1-skeleton of the
  polyhedron, whose edges are the edges of the polyhedron);
* a finite face set `Face` and the `dual` graph on it (two faces are adjacent when they
  share an edge);
* the incidence bijection `edgeEquiv` matching every edge of the polyhedron with the dual
  edge joining the two faces it separates.

The input coming from convexity (equivalently: from the surface being a sphere) is the
classical *tree–cotree decomposition*: the edge set of a polyhedron splits into a spanning
tree `T` of the skeleton and, on the complementary edges, a spanning tree `D` of the dual
graph. Given that decomposition, Euler's formula is a counting identity, obtained from
Mathlib's `SimpleGraph.IsTree.card_edgeFinset` (`|E(T)| + 1 = |V|` for a tree `T`) applied
to `T` and to `D`. -/
theorem euler_polyhedron {Vertex Face : Type*} [Fintype Vertex] [Fintype Face]
    {skeleton T : SimpleGraph Vertex} {dual D : SimpleGraph Face}
    [Fintype skeleton.edgeSet] [Fintype dual.edgeSet]
    [Fintype T.edgeSet] [Fintype D.edgeSet]
    (edgeEquiv : skeleton.edgeSet ≃ dual.edgeSet)
    (hT : T ≤ skeleton) (hTtree : T.IsTree)
    (hD : D ≤ dual) (hDtree : D.IsTree)
    (hcotree : ∀ e : skeleton.edgeSet,
      (edgeEquiv e : Sym2 Face) ∈ D.edgeSet ↔ (e : Sym2 Vertex) ∉ T.edgeSet) :
    Fintype.card Vertex + Fintype.card Face = Fintype.card skeleton.edgeSet + 2 := by
  classical
  -- the tree edges, counted inside the edge set of the skeleton
  have hTcard : Fintype.card {e : skeleton.edgeSet // (e : Sym2 Vertex) ∈ T.edgeSet}
      = Fintype.card T.edgeSet := Fintype.card_congr (edgeSubtypeEquiv hT)
  -- the cotree edges biject with the edges of the dual tree
  have hDcard : Fintype.card {e : skeleton.edgeSet // (e : Sym2 Vertex) ∉ T.edgeSet}
      = Fintype.card D.edgeSet := by
    refine Fintype.card_congr (Equiv.trans ?_ (edgeSubtypeEquiv hD))
    exact Equiv.subtypeEquiv (p := fun e : skeleton.edgeSet => (e : Sym2 Vertex) ∉ T.edgeSet)
      (q := fun f : dual.edgeSet => (f : Sym2 Face) ∈ D.edgeSet) edgeEquiv
      (fun e => (hcotree e).symm)
  -- splitting the skeleton edges into tree edges and cotree edges
  have hsplit : Fintype.card {e : skeleton.edgeSet // (e : Sym2 Vertex) ∈ T.edgeSet}
      + Fintype.card {e : skeleton.edgeSet // (e : Sym2 Vertex) ∉ T.edgeSet}
      = Fintype.card skeleton.edgeSet := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl _)
  -- Mathlib's count of the edges of a tree
  have hTree : Fintype.card T.edgeSet + 1 = Fintype.card Vertex := by
    have := hTtree.card_edgeFinset
    rwa [SimpleGraph.edgeFinset_card] at this
  have hDTree : Fintype.card D.edgeSet + 1 = Fintype.card Face := by
    have := hDtree.card_edgeFinset
    rwa [SimpleGraph.edgeFinset_card] at this
  omega

/-- The one-point graph is a tree. -/
lemma bot_isTree_fin_one : (⊥ : SimpleGraph (Fin 1)).IsTree := by
  constructor
  · exact ⟨fun a b => (Subsingleton.elim a b) ▸ SimpleGraph.Reachable.refl a⟩
  · intro a p hp
    cases p with
    | nil => exact hp.ne_nil rfl
    | cons h _ => exact h.elim

/-- The hypotheses of `Chem.euler_polyhedron` are satisfiable: the degenerate polyhedron
with a single vertex, no edge and a single face. (A sanity check that the statement is not
vacuous.) -/
example : Fintype.card (Fin 1) + Fintype.card (Fin 1)
    = Fintype.card (⊥ : SimpleGraph (Fin 1)).edgeSet + 2 :=
  euler_polyhedron (Equiv.refl _) le_rfl bot_isTree_fin_one le_rfl bot_isTree_fin_one
    (fun e => absurd e.2 (by simp))

/-! ### A concrete polyhedron: the tetrahedron

We check that the hypotheses of `Chem.euler_polyhedron` really are met by an honest convex
polyhedron. For the tetrahedron the 1-skeleton is the complete graph `K₄` on `Fin 4`, and,
labelling each face by the vertex it misses, the dual graph is again `K₄`: two faces share
an edge exactly when the two vertices labelling them are distinct. Under this labelling the
edge `{a,b}` of the tetrahedron separates the two faces labelled by the *complementary*
pair, so the incidence bijection is the complementation involution `Chem.Tetrahedron.cmap`
on pairs. The star at the vertex `0` is a spanning tree of `K₄`, and the complementary
edges `{1,2}, {1,3}, {2,3}` correspond to the dual edges `{0,3}, {0,2}, {0,1}`, i.e. to the
star at `0` in the dual: a tree–cotree decomposition. Euler's formula then gives
`4 - 6 + 4 = 2`. -/
namespace Tetrahedron

/-- Complementation on pairs of vertices of the tetrahedron: `{a,b} ↦ {c,d}` where `{c,d}`
is the complementary pair (and `{a,a} ↦ {a,a}`). -/
def cf : Fin 4 → Fin 4 → Sym2 (Fin 4) :=
  ![![s(0,0), s(2,3), s(1,3), s(1,2)],
    ![s(2,3), s(1,1), s(0,3), s(0,2)],
    ![s(1,3), s(0,3), s(2,2), s(0,1)],
    ![s(1,2), s(0,2), s(0,1), s(3,3)]]

lemma cf_symm : ∀ a b : Fin 4, cf a b = cf b a := by
  intro a b; fin_cases a <;> fin_cases b <;> rfl

/-- The complementation involution on unordered pairs of vertices. -/
def cmap : Sym2 (Fin 4) → Sym2 (Fin 4) := Sym2.lift ⟨cf, cf_symm⟩

lemma cmap_mk (a b : Fin 4) : cmap s(a, b) = cf a b := rfl

lemma cmap_invol : Function.Involutive cmap := by
  intro e
  induction e using Sym2.ind with
  | _ a b => fin_cases a <;> fin_cases b <;> simp [cmap_mk, cf]

lemma cmap_notDiag (e : Sym2 (Fin 4)) : ¬ (cmap e).IsDiag ↔ ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b => fin_cases a <;> fin_cases b <;> simp [cmap_mk, cf]

/-- The star at the vertex `0`: a spanning tree of `K₄`. -/
def star : SimpleGraph (Fin 4) := SimpleGraph.fromRel (fun a _ => a = 0)

instance : DecidableRel star.Adj := fun a b => by unfold star; infer_instance

lemma star_adj (a b : Fin 4) : star.Adj a b ↔ a ≠ b ∧ (a = 0 ∨ b = 0) := by
  simp [star, SimpleGraph.fromRel_adj]

lemma star_reach (x : Fin 4) : star.Reachable 0 x := by
  rcases eq_or_ne (0 : Fin 4) x with rfl | hx
  · rfl
  · exact SimpleGraph.Adj.reachable ((star_adj 0 x).2 ⟨hx, Or.inl rfl⟩)

lemma star_connected : star.Connected :=
  SimpleGraph.Connected.mk (fun a b => (star_reach a).symm.trans (star_reach b))

lemma star_card_edges : Nat.card star.edgeSet = 3 := by
  have h := star.sum_degrees_eq_twice_card_edges
  have h2 : ∑ v : Fin 4, star.degree v = 6 := by decide
  rw [h2] at h
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega

lemma star_isTree : star.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨star_connected, ?_⟩
  rw [star_card_edges, Nat.card_eq_fintype_card, Fintype.card_fin]

lemma star_le_top : star ≤ (⊤ : SimpleGraph (Fin 4)) := le_top

lemma mem_top_edgeSet (e : Sym2 (Fin 4)) :
    e ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet ↔ ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b => simp

lemma card_top_edges : Fintype.card (⊤ : SimpleGraph (Fin 4)).edgeSet = 6 := by
  have h := (⊤ : SimpleGraph (Fin 4)).sum_degrees_eq_twice_card_edges
  have h2 : ∑ v : Fin 4, (⊤ : SimpleGraph (Fin 4)).degree v = 12 := by decide
  rw [h2, SimpleGraph.edgeFinset_card] at h
  omega

/-- The incidence bijection between edges of the tetrahedron and edges of its dual. -/
def edgeEquiv : (⊤ : SimpleGraph (Fin 4)).edgeSet ≃ (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  Equiv.subtypeEquiv (Function.Involutive.toPerm cmap cmap_invol)
    (fun e => by
      simp only [mem_top_edgeSet, Function.Involutive.coe_toPerm]
      exact (cmap_notDiag e).symm)

lemma edgeEquiv_coe (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    (edgeEquiv e : Sym2 (Fin 4)) = cmap (e : Sym2 (Fin 4)) := rfl

/-- The tree–cotree condition: an edge of the tetrahedron avoids the vertex `0` exactly
when the dual edge it corresponds to meets the face `0`. -/
lemma tree_cotree (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    (edgeEquiv e : Sym2 (Fin 4)) ∈ star.edgeSet ↔ (e : Sym2 (Fin 4)) ∉ star.edgeSet := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
      rw [mem_top_edgeSet] at he
      fin_cases a <;> fin_cases b <;>
        simp_all [edgeEquiv_coe, cmap_mk, cf, SimpleGraph.mem_edgeSet, star_adj]

/-- **Euler's formula for the tetrahedron**, an instance of `Chem.euler_polyhedron`: with
`Fintype.card (Fin 4) = 4` vertices and faces and `Chem.Tetrahedron.card_top_edges` (`= 6`)
edges, this reads `4 - 6 + 4 = 2`. -/
theorem euler : Fintype.card (Fin 4) + Fintype.card (Fin 4)
    = Fintype.card (⊤ : SimpleGraph (Fin 4)).edgeSet + 2 :=
  Chem.euler_polyhedron edgeEquiv star_le_top star_isTree star_le_top star_isTree tree_cotree

end Tetrahedron

/-- **Fullerene cages have exactly 12 pentagonal faces.**

If a cage is trivalent (`3 * V = 2 * E`, every carbon atom has three neighbours) and every
face is a pentagon or a hexagon (`F = p + h` and `5 * p + 6 * h = 2 * E`), then Euler's
formula `V + F = E + 2` forces `p = 12`. -/
theorem fullerene_twelve_pentagons {V E F p h : ℕ} (hEuler : V + F = E + 2)
    (htrivalent : 3 * V = 2 * E) (hfaces : F = p + h) (hedges : 5 * p + 6 * h = 2 * E) :
    p = 12 := by omega

/-- Buckminsterfullerene C₆₀: 60 vertices, 90 edges, 32 faces (12 pentagons, 20 hexagons)
satisfies Euler's formula. -/
example : 60 + 32 = 90 + 2 := by norm_num

end Chem

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

