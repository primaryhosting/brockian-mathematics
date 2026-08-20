/-
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
## Euler's polyhedron formula `V - E + F = 2`

A convex polyhedron (for instance a fullerene cage such as C₆₀) is described combinatorially by

* its *1-skeleton* `G`, the simple graph of vertices and edges of the polyhedron;
* its *dual graph* `D`, whose vertices are the faces of the polyhedron and whose edges are in
  bijection with the edges of `G` (an edge of `G` is dual to the edge joining the two faces
  meeting along it).

Planarity of the 1-skeleton of a convex polyhedron (Steinitz) is used, in the classical proof of
Euler's formula, through the *tree–cotree* (spanning tree / dual spanning tree) decomposition:
one can choose a spanning tree `T` of `G` such that the duals of the edges **not** in `T` form a
spanning tree `S` of the dual graph `D`.  This is exactly the hypothesis packaged below, and the
conclusion is Euler's formula

  `#vertices - #edges + #faces = 2`.

The only nontrivial input is the Mathlib lemma
`SimpleGraph.isTree_iff_connected_and_card` (equivalently `SimpleGraph.IsTree.card_edgeFinset`):
a tree on `n` vertices has `n - 1` edges.
-/

namespace Chem

open SimpleGraph

/-- The edges of a subgraph `H ≤ G`, seen as a sub-collection of the edges of `G`. -/
def edgeSubtypeEquiv {V : Type*} {G H : SimpleGraph V} (h : H ≤ G) :
    {e : G.edgeSet // (e : Sym2 V) ∈ H.edgeSet} ≃ H.edgeSet where
  toFun e := ⟨e.1.1, e.2⟩
  invFun t := ⟨⟨t.1, SimpleGraph.edgeSet_mono h t.2⟩, t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Euler's polyhedron formula.**

Let `G` be the 1-skeleton of a convex polyhedron (vertices `Vtx`, edges `G.edgeSet`) and let `D`
be its dual graph (vertices `Fce`, the faces of the polyhedron), together with the duality
bijection `dual` between the edges of `G` and the edges of `D`.  Assume a tree–cotree
decomposition: `T` is a spanning tree of `G`, `S` is a spanning tree of `D`, and an edge of `G`
belongs to `T` if and only if its dual edge does *not* belong to `S`.  Then

  `V - E + F = 2`. -/
theorem euler_polyhedron {Vtx Fce : Type*} [Finite Vtx] [Finite Fce]
    {G T : SimpleGraph Vtx} {D S : SimpleGraph Fce}
    (hTG : T ≤ G) (hSD : S ≤ D) (hT : T.IsTree) (hS : S.IsTree)
    (dual : G.edgeSet ≃ D.edgeSet)
    (hdual : ∀ e : G.edgeSet, (e : Sym2 Vtx) ∈ T.edgeSet ↔ (dual e : Sym2 Fce) ∉ S.edgeSet) :
    (Nat.card Vtx : ℤ) - Nat.card G.edgeSet + Nat.card Fce = 2 := by
  classical
  have hVtree : Nat.card T.edgeSet + 1 = Nat.card Vtx :=
    ((isTree_iff_connected_and_card).1 hT).2
  have hFtree : Nat.card S.edgeSet + 1 = Nat.card Fce :=
    ((isTree_iff_connected_and_card).1 hS).2
  -- split the edges of `G` into tree edges and cotree edges
  have hsplit : Nat.card G.edgeSet
      = Nat.card {e : G.edgeSet // (e : Sym2 Vtx) ∈ T.edgeSet}
        + Nat.card {e : G.edgeSet // (e : Sym2 Vtx) ∉ T.edgeSet} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun e : G.edgeSet => (e : Sym2 Vtx) ∈ T.edgeSet)).symm
  have htree : Nat.card {e : G.edgeSet // (e : Sym2 Vtx) ∈ T.edgeSet} = Nat.card T.edgeSet :=
    Nat.card_congr (edgeSubtypeEquiv hTG)
  have hcotree : Nat.card {e : G.edgeSet // (e : Sym2 Vtx) ∉ T.edgeSet} = Nat.card S.edgeSet := by
    refine Nat.card_congr ((Equiv.subtypeEquiv dual ?_).trans (edgeSubtypeEquiv hSD))
    intro e
    rw [hdual e, not_not]
  rw [hsplit, htree, hcotree]
  omega

/-!
### The hypotheses are satisfiable: the tetrahedron

The simplest convex polyhedron, the tetrahedron, has complete graph `K₄` as 1-skeleton and is
self-dual.  The path `0 - 1 - 2 - 3` is a spanning tree of `K₄` whose complement `2 - 0 - 3 - 1`
is again a spanning tree, so the tree–cotree hypothesis of `Chem.euler_polyhedron` is satisfiable,
and it yields `4 - 6 + 4 = 2`.
-/

/-- The spanning path `0 - 1 - 2 - 3` inside the complete graph on four vertices. -/
def tetraTree : SimpleGraph (Fin 4) where
  Adj a b := ((a : ℕ) + 1 = (b : ℕ)) ∨ ((b : ℕ) + 1 = (a : ℕ))
  symm := by intro a b h; tauto
  loopless := ⟨by intro a h; omega⟩

instance : DecidableRel tetraTree.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma tetraTree_isTree : tetraTree.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨by decide, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

lemma tetraTree_compl_isTree : (tetraTreeᶜ).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨by decide, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

lemma card_tetrahedron_edges : Nat.card (⊤ : SimpleGraph (Fin 4)).edgeSet = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Euler's formula for the tetrahedron, obtained from `Chem.euler_polyhedron`:
`4 - 6 + 4 = 2`.  In particular the hypotheses of `Chem.euler_polyhedron` are not vacuous. -/
theorem tetrahedron_euler :
    (Nat.card (Fin 4) : ℤ) - Nat.card (⊤ : SimpleGraph (Fin 4)).edgeSet + Nat.card (Fin 4) = 2 :=
  euler_polyhedron le_top le_top tetraTree_isTree tetraTree_compl_isTree (Equiv.refl _)
    (by decide)

/-- **Fullerenes have exactly twelve pentagonal faces.**

If a polyhedral cage satisfies Euler's formula, every vertex has degree three (`3V = 2E`, the
usual chemical bonding pattern of a fullerene) and every face is a pentagon or a hexagon
(`p` pentagons and `h` hexagons, so `5p + 6h = 2E` and `p + h = F`), then `p = 12`. -/
theorem fullerene_pentagon_count (V E F p h : ℕ)
    (heuler : (V : ℤ) - E + F = 2) (hdeg : 3 * V = 2 * E)
    (hfaces : p + h = F) (hedges : 5 * p + 6 * h = 2 * E) :
    p = 12 := by
  omega

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

