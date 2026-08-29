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

def FiniteFourColorTheorem : Prop :=
  ∀ {V : Type*} [Finite V] (G : SimpleGraph V), Planar G → G.Colorable 4

/-! ## Basic closure properties of planarity -/

/-- A subgraph (on the same vertex type) of a planar graph is planar. -/
