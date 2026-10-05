/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command, so the header above is a plain
-- block comment and is repeated below as the module docstring.)
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

/-! ## Planarity

We record a faithful topological definition of planarity: a *plane drawing* of a
simple graph `G` consists of an injective placement of the vertices in the plane
together with, for each edge, an arc (a homeomorphic copy of the unit interval)
joining the images of its endpoints, such that arcs meet each other only in
common endpoints and meet vertex points only in their own endpoints. -/

/-- A drawing of `G` in the plane: vertices are distinct points, edges are arcs
joining their endpoints, and two arcs meet only at points that are images of
common endpoints. -/
structure PlaneDrawing (G : SimpleGraph V) where
  /-- the position of each vertex in the plane -/
  pt : V → ℝ × ℝ
  /-- distinct vertices get distinct points -/
  pt_inj : Function.Injective pt
  /-- the arc drawn for each edge (as a subset of the plane) -/
  arc : ∀ ⦃u v : V⦄, G.Adj u v → Set (ℝ × ℝ)
  /-- an edge is drawn by the same arc in either direction -/
  arc_symm : ∀ ⦃u v : V⦄ (h : G.Adj u v), arc h.symm = arc h
  /-- each arc is a homeomorphic image of `[0,1]` running from `pt u` to `pt v` -/
  arc_isArc : ∀ ⦃u v : V⦄ (h : G.Adj u v),
    ∃ f : C(unitInterval, ℝ × ℝ), Function.Injective f ∧ Set.range f = arc h ∧
      f 0 = pt u ∧ f 1 = pt v
  /-- an arc contains no vertex point other than those of its own endpoints -/
  arc_mem_pt : ∀ ⦃u v : V⦄ (h : G.Adj u v) (w : V), pt w ∈ arc h ↔ (w = u ∨ w = v)
  /-- two arcs of different edges meet only at points of shared endpoints -/
  arc_inter : ∀ ⦃u v u' v' : V⦄ (h : G.Adj u v) (h' : G.Adj u' v'),
    s(u, v) ≠ s(u', v') →
      arc h ∩ arc h' ⊆ pt '' (({u, v} : Set V) ∩ ({u', v'} : Set V))

/-- A simple graph is *planar* if it admits a drawing in the plane. -/

theorem Planar.mono {G H : SimpleGraph V} (hHG : H ≤ G) (hG : Planar G) : Planar H := by
  obtain ⟨D⟩ := hG
  refine ⟨{ pt := D.pt
            pt_inj := D.pt_inj
            arc := fun _ _ h => D.arc (hHG h)
            arc_symm := fun _ _ h => D.arc_symm (hHG h)
            arc_isArc := fun _ _ h => D.arc_isArc (hHG h)
            arc_mem_pt := fun _ _ h w => D.arc_mem_pt (hHG h) w
            arc_inter := fun _ _ _ _ h h' hne => D.arc_inter (hHG h) (hHG h') hne }⟩

/-- The empty graph on `Fin n` is planar: place the vertices along a line. -/
