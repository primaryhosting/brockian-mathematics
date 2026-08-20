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
