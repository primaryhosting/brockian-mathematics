import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Frontier

universe u

variable {V : Type u}

/-! ## Plane straight-line drawings

Mathlib (at the pinned commit) contains no theory of planar graphs at all, so we
first have to say what "planar" means.

We use the *straight-line* (Fáry) formulation: a finite simple graph is planar
exactly when it can be drawn in the plane with vertices at distinct points and
edges drawn as straight segments which meet only at shared endpoints.  By
Fáry's theorem this is equivalent to the usual topological definition for
finite simple graphs, and it has the advantage of being completely elementary
to state. -/

/-- The open straight segment in `ℝ²` drawn for an (unordered) edge `e`, when the
vertices are placed by `p`. -/

lemma seg_mk (p : V → ℝ × ℝ) (a b : V) : seg p s(a, b) = openSegment ℝ (p a) (p b) := rfl

/-- `p : V → ℝ × ℝ` is a plane straight-line drawing of `G`: the vertices are placed
at distinct points, the open segments of two distinct edges are disjoint (so edges
meet only at common endpoints), and no vertex lies in the interior of an edge. -/
structure IsPlaneDrawing (G : SimpleGraph V) (p : V → ℝ × ℝ) : Prop where
  /-- distinct vertices get distinct points -/
  inj : Function.Injective p
  /-- distinct edges only meet at their endpoints -/
  edge_disjoint : ∀ e ∈ G.edgeSet, ∀ f ∈ G.edgeSet, e ≠ f → Disjoint (seg p e) (seg p f)
  /-- no vertex lies in the interior of an edge -/
  vertex_notMem : ∀ (v : V), ∀ e ∈ G.edgeSet, p v ∉ seg p e

/-- A simple graph is *planar* when it admits a plane straight-line drawing. -/
