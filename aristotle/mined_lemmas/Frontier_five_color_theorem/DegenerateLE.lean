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

set_option grind.warning false

/-!
# Planar graphs and colourings

This file sets up a faithful (topological) notion of planarity for simple graphs — a
drawing of the graph in the plane `ℝ × ℝ` where vertices are distinct points and edges
are arcs meeting only at common endpoints — and proves a base case of the five colour
theorem.
-/

namespace SimpleGraph

variable {V : Type*}

/-- A drawing of a simple graph `G` in the plane: an injective placement of the vertices
as points of `ℝ × ℝ`, together with, for every edge, an arc (a continuous injective image
of the unit interval) joining the two endpoints, such that two distinct arcs meet only in
the images of their common endpoints, and a vertex point lies on an arc only if it is an
endpoint of the corresponding edge. -/
structure PlanarEmbedding (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  point : V → ℝ × ℝ
  /-- Distinct vertices get distinct points. -/
  point_inj : Function.Injective point
  /-- The set of points of the plane covered by the arc drawn for an edge. -/
  arc : Sym2 V → Set (ℝ × ℝ)
  /-- Each edge is drawn as an arc: a continuous injective image of `[0,1]` whose
  endpoints are the points of the two ends of the edge. -/
  arc_isArc : ∀ e ∈ G.edgeSet, ∃ f : unitInterval → ℝ × ℝ,
    Continuous f ∧ Function.Injective f ∧ Set.range f = arc e ∧
      Sym2.map point e = s(f 0, f 1)
  /-- Two distinct arcs meet only at points of common endpoints. -/
  arc_inter : ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, e ≠ e' →
    arc e ∩ arc e' ⊆ point '' {v | v ∈ e ∧ v ∈ e'}
  /-- A vertex point lying on an arc must be an endpoint of that edge. -/
  point_mem_arc : ∀ e ∈ G.edgeSet, ∀ v : V, point v ∈ arc e → v ∈ e

/-- A simple graph is *planar* if it can be drawn in the plane. -/

def DegenerateLE (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, ((s.erase v).filter (fun w => G.Adj v w)).card ≤ k

/-- Any graph on at most `k + 1` vertices is `k`-degenerate. -/
