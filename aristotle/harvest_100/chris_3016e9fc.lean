import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
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

namespace Chem

/-!
## Euler's polyhedron formula `V - E + F = 2`

A convex polyhedron (a fullerene cage, say) is described combinatorially by its
*skeleton* `G` — the graph of vertices and edges — together with its *dual graph* `D`,
whose nodes are the faces of the polyhedron and whose edges record which pairs of
faces share an edge of the polyhedron.  Each edge of the polyhedron is at the same
time an edge of `G` and an edge of `D`, which is recorded by the bijection
`dualEdge : G.edgeSet ≃ D.edgeSet`.

The fact that the surface of the polyhedron is a *sphere* (and not, say, a torus)
is expressed by the classical **tree–cotree** (spanning tree / dual spanning tree)
decomposition: there is a spanning tree `T` of the skeleton such that the edges *not*
in `T` are exactly the edges whose duals form a spanning tree `C` of the dual graph.
Both of these are genuine spanning trees, i.e. connected and acyclic graphs on the
whole vertex (resp. face) set.

From this data Euler's formula `V - E + F = 2` follows: the primal tree has `V - 1`
edges, the dual tree has `F - 1` edges, and every edge lies in exactly one of the two
families.
-/

/-- **Euler's polyhedron formula.**  For a polyhedron presented by its skeleton `G`
(vertices `V`, edges `G.edgeFinset`) and dual graph `D` (nodes = faces), with the
sphere condition given by a tree–cotree decomposition `(T, C)`, one has
`V - E + F = 2`. -/
theorem euler_polyhedron
    {V F : Type*} [Fintype V] [Fintype F]
    (G T : SimpleGraph V) (D C : SimpleGraph F)
    (hTG : T ≤ G) (hCD : C ≤ D)
    (hT : T.IsTree) (hC : C.IsTree)
    (dualEdge : G.edgeSet ≃ D.edgeSet)
    (hdual : ∀ e : G.edgeSet, ((dualEdge e : Sym2 F) ∈ C.edgeSet ↔ (e : Sym2 V) ∉ T.edgeSet)) :
    (Fintype.card V : ℤ) - (Fintype.card G.edgeSet : ℤ) + (Fintype.card F : ℤ) = 2 := by
  classical
  -- the edges of `G` lying in `T` are in bijection with the edges of `T`
  have e₁ : {e : G.edgeSet // (e : Sym2 V) ∈ T.edgeSet} ≃ T.edgeSet :=
    { toFun := fun e => ⟨(e : G.edgeSet), e.2⟩
      invFun := fun e => ⟨⟨(e : Sym2 V), SimpleGraph.edgeSet_mono hTG e.2⟩, e.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  -- the edges of `G` not in `T` are in bijection with the edges of `C`
  have e₂ : {e : G.edgeSet // (e : Sym2 V) ∉ T.edgeSet} ≃ C.edgeSet := by
    refine (Equiv.subtypeEquiv (p := fun e : G.edgeSet => (e : Sym2 V) ∉ T.edgeSet)
      (q := fun f : D.edgeSet => (f : Sym2 F) ∈ C.edgeSet) dualEdge
      (fun e => (hdual e).symm)).trans ?_
    exact
    { toFun := fun f => ⟨(f : Sym2 F), f.2⟩
      invFun := fun f => ⟨⟨(f : Sym2 F), SimpleGraph.edgeSet_mono hCD f.2⟩, f.2⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  have hle := Fintype.card_subtype_le (fun e : G.edgeSet => (e : Sym2 V) ∈ T.edgeSet)
  have hcompl := Fintype.card_subtype_compl (fun e : G.edgeSet => (e : Sym2 V) ∈ T.edgeSet)
  have hsplit :
      Fintype.card {e : G.edgeSet // (e : Sym2 V) ∈ T.edgeSet}
        + Fintype.card {e : G.edgeSet // (e : Sym2 V) ∉ T.edgeSet}
        = Fintype.card G.edgeSet := by omega
  have hTcard : Fintype.card T.edgeSet + 1 = Fintype.card V := by
    simpa [SimpleGraph.edgeFinset_card] using hT.card_edgeFinset
  have hCcard : Fintype.card C.edgeSet + 1 = Fintype.card F := by
    simpa [SimpleGraph.edgeFinset_card] using hC.card_edgeFinset
  have h1 : Fintype.card {e : G.edgeSet // (e : Sym2 V) ∈ T.edgeSet} = Fintype.card T.edgeSet :=
    Fintype.card_congr e₁
  have h2 : Fintype.card {e : G.edgeSet // (e : Sym2 V) ∉ T.edgeSet} = Fintype.card C.edgeSet :=
    Fintype.card_congr e₂
  rw [h1, h2] at hsplit
  omega

/-!
## A concrete instance: the tetrahedron

To see that the hypotheses of `Chem.euler_polyhedron` are satisfiable (and are the
right ones), we instantiate them for the tetrahedron: its skeleton is the complete
graph `K₄` on the four vertices, its four faces are labelled by the opposite vertex,
so that the dual graph is again `K₄`, and the edge `{a,b}` of the skeleton is shared
by the two faces `{c,d}` complementary to it.  The spanning tree (and, under the
duality, the cotree) is the star centred at the vertex `0`.
-/

/-- Auxiliary description of the complementary pair of a pair in `Fin 4`. -/
private def complAux : ℕ → ℕ → Sym2 (Fin 4)
  | 0, 1 => s(2, 3) | 1, 0 => s(2, 3)
  | 0, 2 => s(1, 3) | 2, 0 => s(1, 3)
  | 0, 3 => s(1, 2) | 3, 0 => s(1, 2)
  | 1, 2 => s(0, 3) | 2, 1 => s(0, 3)
  | 1, 3 => s(0, 2) | 3, 1 => s(0, 2)
  | 2, 3 => s(0, 1) | 3, 2 => s(0, 1)
  | 0, 0 => s(0, 0) | 1, 1 => s(1, 1) | 2, 2 => s(2, 2) | _, _ => s(3, 3)

/-- The map sending a pair of vertices of the tetrahedron to the complementary pair,
i.e. an edge of the skeleton to the pair of faces meeting along it. -/
def tetraCompl : Sym2 (Fin 4) → Sym2 (Fin 4) :=
  Sym2.lift ⟨fun a b => complAux a.val b.val, by decide⟩

/-- The edge/face-pair correspondence of the tetrahedron, as a permutation of pairs. -/
def tetraComplPerm : Equiv.Perm (Sym2 (Fin 4)) :=
  ⟨tetraCompl, tetraCompl, by decide, by decide⟩

/-- The star centred at vertex `0`: the spanning tree of the tetrahedron we use. -/
def tetraStar : SimpleGraph (Fin 4) := SimpleGraph.fromRel (fun a _ => a = 0)

instance : DecidableRel tetraStar.Adj := fun a b => by
  unfold tetraStar SimpleGraph.fromRel; infer_instance

lemma tetraStar_le_top : tetraStar ≤ (⊤ : SimpleGraph (Fin 4)) := fun _ _ h => h.ne

lemma tetraStar_connected : tetraStar.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨0⟩⟩
  have key : ∀ w : Fin 4, tetraStar.Reachable 0 w := by
    intro w
    by_cases h : w = 0
    · subst h; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (by simp [tetraStar, SimpleGraph.fromRel, Ne.symm h])
  exact fun u v => ((key u).symm).trans (key v)

lemma tetraStar_isTree : tetraStar.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨tetraStar_connected, ?_⟩
  simp only [Nat.card_eq_fintype_card]
  decide

/-- The duality between edges of the tetrahedron's skeleton and edges of its dual graph. -/
def tetraDualEdge :
    (⊤ : SimpleGraph (Fin 4)).edgeSet ≃ (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  Equiv.subtypeEquiv tetraComplPerm (by decide)

/-- **Euler's formula for the tetrahedron**, obtained by instantiating
`Chem.euler_polyhedron`: `4 - 6 + 4 = 2`. -/
theorem euler_tetrahedron :
    (Fintype.card (Fin 4) : ℤ) - (Fintype.card (⊤ : SimpleGraph (Fin 4)).edgeSet : ℤ)
      + (Fintype.card (Fin 4) : ℤ) = 2 := by
  have h := euler_polyhedron (⊤ : SimpleGraph (Fin 4)) tetraStar (⊤ : SimpleGraph (Fin 4))
    tetraStar tetraStar_le_top tetraStar_le_top tetraStar_isTree tetraStar_isTree tetraDualEdge
    (by decide)
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h

/-- Sanity check on the numbers: the tetrahedron really has `6` edges. -/
example : Fintype.card (⊤ : SimpleGraph (Fin 4)).edgeSet = 6 := by decide

/-!
## A chemical consequence: every fullerene has exactly 12 pentagons

A fullerene cage is a convex polyhedron all of whose vertices have degree `3`
(each carbon atom has three neighbours) and all of whose faces are pentagons or
hexagons.  Counting incidences gives `2E = 3V` and `2E = 5p + 6h`, where `p` and `h`
are the numbers of pentagonal and hexagonal faces; Euler's formula then forces
`p = 12`, independently of the size of the cage.
-/

/-- **Twelve pentagons.**  For a polyhedron with all vertices of degree three whose
faces are pentagons and hexagons, Euler's formula `V - E + F = 2` forces the number
of pentagons to be exactly `12`. -/
theorem fullerene_twelve_pentagons {v e f p h : ℕ}
    (hdeg : 2 * e = 3 * v) (hfaces : 2 * e = 5 * p + 6 * h) (hf : f = p + h)
    (heuler : (v : ℤ) - (e : ℤ) + (f : ℤ) = 2) : p = 12 := by
  omega

end Chem

