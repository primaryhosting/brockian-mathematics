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

universe u

namespace Frontier

/-- The Euclidean plane, in which planar graphs are drawn. -/
abbrev Plane : Type := ℝ × ℝ

/-- A *plane drawing* of a simple graph `G`: an injective placement of the vertices in the
plane together with, for every edge, an arc (a homeomorphic image of `[0,1]`) joining the
positions of its endpoints, such that arcs meet the vertex set only at their own endpoints and
two arcs belonging to distinct edges meet only at common endpoints. -/
structure Drawing {V : Type*} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  pos : V → Plane
  /-- Distinct vertices are drawn at distinct points. -/
  pos_injective : Function.Injective pos
  /-- The point set of the arc drawn for the (unordered) edge `{u, v}`. -/
  arc : V → V → Set Plane
  /-- The arc of an edge does not depend on the order of its endpoints. -/
  arc_symm : ∀ u v : V, arc u v = arc v u
  /-- The arc of an edge is a simple curve running from one endpoint to the other. -/
  arc_isArc : ∀ u v : V, G.Adj u v →
    ∃ f : ℝ → Plane, ContinuousOn f (Set.Icc 0 1) ∧ Set.InjOn f (Set.Icc 0 1) ∧
      f 0 = pos u ∧ f 1 = pos v ∧ arc u v = f '' Set.Icc 0 1
  /-- An arc passes through no vertices other than its own endpoints. -/
  arc_inter_pos : ∀ u v : V, G.Adj u v → ∀ w : V, pos w ∈ arc u v → w = u ∨ w = v
  /-- Two arcs belonging to distinct edges meet only at common endpoints. -/
  arc_inter_arc : ∀ u v x y : V, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
    ∀ p ∈ arc u v ∩ arc x y, ∃ w : V, (w = u ∨ w = v) ∧ (w = x ∨ w = y) ∧ p = pos w

/-- A graph is *planar* when it admits a plane drawing. -/

theorem fourColorStatement_iff_fin : FourColorStatement.{0} ↔ FourColorStatementFin :=
  ⟨fun h _ H hH => h H hH, fun h _ G hG => four_color_statement_of_fin h G hG⟩

end Frontier

