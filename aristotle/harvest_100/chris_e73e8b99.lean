import Mathlib

/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A convex polyhedron (for instance a fullerene cage such as C₆₀) gives rise to a *plane map*:

* a graph `G` on the set `Vt` of vertices;
* the dual graph `D` on the set `Ft` of faces;
* a bijection `dual` between the edges of `G` and the edges of `D` — each edge of the
  polyhedron is shared by exactly two faces, and dually.

Planarity (i.e. the fact that the map lives on a sphere) is encoded by the classical
*interdigitating spanning trees* property: there is a spanning tree `T` of the graph such
that the duals of the remaining edges form a spanning tree of the dual graph.  This is the
combinatorial content of planarity used in the standard proof of Euler's formula, and it is
the hypothesis of `Chem.euler_polyhedron` below, whose conclusion is `V - E + F = 2`.

The hypotheses are not vacuous: `Chem.tetrahedron_euler` verifies them for the tetrahedron
(whose graph and dual graph are both `K₄`), and `Chem.fullerene_twelve_pentagons` derives
from Euler's formula the chemical fact that a trivalent cage whose faces are pentagons and
hexagons has exactly twelve pentagons.
-/

namespace Chem

open SimpleGraph

/-- For a set `S` of edges of a graph `H` spanning a tree, `#S + 1 = #vertices`. -/
private theorem ncard_edges_of_isTree {A : Type*} [Finite A] (H : SimpleGraph A)
    (S : Set (Sym2 A)) (hS : S ⊆ H.edgeSet) (h : (SimpleGraph.fromEdgeSet S).IsTree) :
    S.ncard + 1 = Nat.card A := by
  have h2 := (SimpleGraph.isTree_iff_connected_and_card).1 h
  have he : (SimpleGraph.fromEdgeSet S).edgeSet = S := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff]
    exact ⟨fun h => h.1, fun h => ⟨h, H.not_isDiag_of_mem_edgeSet (hS h)⟩⟩
  rw [he] at h2
  exact h2.2

/-- **Euler's polyhedron formula** `V - E + F = 2`.

`G` is the graph of the polyhedron on the vertex set `Vt`, `D` is its dual graph on the set
`Ft` of faces, and `dual` matches up the edges of `G` with the edges of `D`.  The planarity
of the map is expressed through the interdigitating spanning trees `T` (of `G`) and
`dual '' (E \ T)` (of `D`). -/
theorem euler_polyhedron {Vt Ft : Type*} [Finite Vt] [Finite Ft]
    (G : SimpleGraph Vt) (D : SimpleGraph Ft) (dual : Sym2 Vt → Sym2 Ft)
    (hbij : Set.BijOn dual G.edgeSet D.edgeSet)
    (T : Set (Sym2 Vt)) (hT : T ⊆ G.edgeSet)
    (hTtree : (SimpleGraph.fromEdgeSet T).IsTree)
    (hDtree : (SimpleGraph.fromEdgeSet (dual '' (G.edgeSet \ T))).IsTree) :
    (Nat.card Vt : ℤ) - Nat.card G.edgeSet + Nat.card Ft = 2 := by
  have h1 : T.ncard + 1 = Nat.card Vt := ncard_edges_of_isTree G T hT hTtree
  have hsub : dual '' (G.edgeSet \ T) ⊆ D.edgeSet :=
    (Set.image_mono Set.diff_subset).trans (by rw [hbij.image_eq])
  have h2 : (dual '' (G.edgeSet \ T)).ncard + 1 = Nat.card Ft :=
    ncard_edges_of_isTree D _ hsub hDtree
  have h3 : (dual '' (G.edgeSet \ T)).ncard = (G.edgeSet \ T).ncard :=
    Set.InjOn.ncard_image (hbij.injOn.mono Set.diff_subset)
  have h4 : (G.edgeSet \ T).ncard + T.ncard = G.edgeSet.ncard :=
    Set.ncard_diff_add_ncard_of_subset hT (Set.toFinite _)
  have h5 : Nat.card G.edgeSet = G.edgeSet.ncard := rfl
  omega

/-!
## The hypotheses are satisfiable: the tetrahedron

The graph of the tetrahedron is `K₄` on `Fin 4`; its four faces are indexed by the opposite
vertices, so its dual graph is again `K₄`, the duality on edges sending an edge `{a,b}` to
the complementary pair.  The star at the vertex `0` is a spanning tree, and the duals of the
three remaining edges again form the star at `0`, a spanning tree of the dual.
-/

/-- The star at the vertex `0`: a spanning tree of `K₄`. -/
def star4 : Set (Sym2 (Fin 4)) := {s(0, 1), s(0, 2), s(0, 3)}

/-- Duality on the edges of the tetrahedron: an edge is sent to the complementary pair of
vertices, i.e. to the pair of faces containing it. -/
def dual4 (e : Sym2 (Fin 4)) : Sym2 (Fin 4) :=
  if e = s(0, 1) then s(2, 3) else
  if e = s(0, 2) then s(1, 3) else
  if e = s(0, 3) then s(1, 2) else
  if e = s(1, 2) then s(0, 3) else
  if e = s(1, 3) then s(0, 2) else s(0, 1)

theorem star4_subset : star4 ⊆ (⊤ : SimpleGraph (Fin 4)).edgeSet := by
  intro e he
  simp only [star4, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with h | h | h <;> subst h <;> decide

theorem star4_isTree : (SimpleGraph.fromEdgeSet star4).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff]
    refine ⟨?_, ⟨0⟩⟩
    have key : ∀ v : Fin 4, (SimpleGraph.fromEdgeSet star4).Reachable 0 v := by
      intro v
      fin_cases v
      · exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (by simp [star4, SimpleGraph.fromEdgeSet_adj])
      · exact SimpleGraph.Adj.reachable (by simp [star4, SimpleGraph.fromEdgeSet_adj])
      · exact SimpleGraph.Adj.reachable (by simp [star4, SimpleGraph.fromEdgeSet_adj])
    intro u v
    exact ((key u).symm).trans (key v)
  · have he : (SimpleGraph.fromEdgeSet star4).edgeSet = star4 := by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext e
      simp only [Set.mem_diff]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      revert h
      induction e using Sym2.ind with
      | _ a b => fin_cases a <;> fin_cases b <;> simp [star4]
    have h3 : Nat.card star4 = 3 := by
      have : star4.ncard = 3 := by
        rw [Set.ncard_eq_three]
        exact ⟨s(0, 1), s(0, 2), s(0, 3), by decide, by decide, by decide, rfl⟩
      exact this
    rw [he, h3]
    simp

theorem dual4_bijOn :
    Set.BijOn dual4 (⊤ : SimpleGraph (Fin 4)).edgeSet (⊤ : SimpleGraph (Fin 4)).edgeSet := by
  have key : ∀ e ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet,
      dual4 e ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet ∧ dual4 (dual4 e) = e := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at he
      fin_cases a <;> fin_cases b <;> simp_all [dual4]
  have hmaps : Set.MapsTo dual4 (⊤ : SimpleGraph (Fin 4)).edgeSet
      (⊤ : SimpleGraph (Fin 4)).edgeSet := fun e he => (key e he).1
  exact Set.InvOn.bijOn ⟨fun e he => (key e he).2, fun e he => (key e he).2⟩ hmaps hmaps

theorem dual4_image_compl : dual4 '' ((⊤ : SimpleGraph (Fin 4)).edgeSet \ star4) = star4 := by
  have hd : (⊤ : SimpleGraph (Fin 4)).edgeSet \ star4 = {s(1, 2), s(1, 3), s(2, 3)} := by
    ext e
    induction e using Sym2.ind with
    | _ a b => fin_cases a <;> fin_cases b <;> simp [star4]
  have e1 : dual4 s(1, 2) = s(0, 3) := by decide
  have e2 : dual4 s(1, 3) = s(0, 2) := by decide
  have e3 : dual4 s(2, 3) = s(0, 1) := by decide
  rw [hd]
  simp only [Set.image_insert_eq, Set.image_singleton, e1, e2, e3]
  ext e
  simp only [star4, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- The hypotheses of `Chem.euler_polyhedron` are satisfiable: the tetrahedron is a plane
map with interdigitating spanning trees, and indeed `4 - 6 + 4 = 2`. -/
theorem tetrahedron_euler :
    (Nat.card (Fin 4) : ℤ) - Nat.card (⊤ : SimpleGraph (Fin 4)).edgeSet
      + Nat.card (Fin 4) = 2 :=
  euler_polyhedron _ _ dual4 dual4_bijOn star4 star4_subset star4_isTree
    (by rw [dual4_image_compl]; exact star4_isTree)

/-!
## Fullerenes: exactly twelve pentagonal faces
-/

/-- Arithmetic consequence of Euler's formula for fullerenes: a trivalent cage (`3V = 2E`)
whose `F = p + h` faces are `p` pentagons and `h` hexagons (`5p + 6h = 2E`) has exactly
twelve pentagons. -/
theorem fullerene_twelve_pentagons {V E F p h : ℕ}
    (hEuler : (V : ℤ) - E + F = 2) (hdeg : 3 * V = 2 * E) (hF : F = p + h)
    (hface : 5 * p + 6 * h = 2 * E) : p = 12 := by
  subst hF
  have : (V : ℤ) - E + (p + h) = 2 := by exact_mod_cast hEuler
  omega

/-- A fullerene cage: a plane map (as in `Chem.euler_polyhedron`) in which every vertex has
degree three and every face is a pentagon or a hexagon has exactly twelve pentagonal faces. -/
theorem fullerene_pentagon_count {Vt Ft : Type*} [Finite Vt] [Finite Ft]
    (G : SimpleGraph Vt) (D : SimpleGraph Ft) (dual : Sym2 Vt → Sym2 Ft)
    (hbij : Set.BijOn dual G.edgeSet D.edgeSet)
    (T : Set (Sym2 Vt)) (hT : T ⊆ G.edgeSet)
    (hTtree : (SimpleGraph.fromEdgeSet T).IsTree)
    (hDtree : (SimpleGraph.fromEdgeSet (dual '' (G.edgeSet \ T))).IsTree)
    (p h : ℕ)
    (hdeg : 3 * Nat.card Vt = 2 * Nat.card G.edgeSet)
    (hfaces : Nat.card Ft = p + h)
    (hsizes : 5 * p + 6 * h = 2 * Nat.card G.edgeSet) : p = 12 :=
  fullerene_twelve_pentagons
    (euler_polyhedron G D dual hbij T hT hTtree hDtree) hdeg hfaces hsizes

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

