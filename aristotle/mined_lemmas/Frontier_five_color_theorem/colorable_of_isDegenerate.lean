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

theorem colorable_of_isDegenerate [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hG : IsDegenerate G k) : G.Colorable (k + 1) := by
  classical
  obtain ⟨c, hc, hcol⟩ := exists_coloring_on G hG Finset.univ
  rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  exact ⟨⟨c, fun {u w} h => hcol u (Finset.mem_univ u) w (Finset.mem_univ w) h⟩, hc⟩

/-! ## The Five Colour Theorem

The full statement — every planar graph is 5-colourable — proceeds by induction on
the number of vertices: a planar graph always has a vertex `v` of degree at most
five, one deletes it, colours the rest by induction, and if all five colours occur
around `v` one recolours along a Kempe chain (which requires the Jordan curve
