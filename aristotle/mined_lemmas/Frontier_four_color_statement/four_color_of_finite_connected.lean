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

theorem four_color_of_finite_connected
    (h : ∀ {W : Type u} [Finite W] (H : SimpleGraph W), IsPlanar H → H.Connected → H.Colorable 4)
    {V : Type u} (G : SimpleGraph V) (hG : IsPlanar G) : G.Colorable 4 :=
  four_color_statement (fun {W} _ H hH => by
    rw [SimpleGraph.colorable_iff_forall_connectedComponents]
    exact fun C => h _ (hH.connectedComponent C) C.connected_toSimpleGraph) G hG

/-- The finite case of the Four Colour Theorem implies the general case. -/
