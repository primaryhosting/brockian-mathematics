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

theorem isDegenerate_of_card_le_five [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard : Fintype.card V ≤ 5) : IsDegenerate G 4 := by
  classical
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  have h1 : ((s.erase v).filter (fun u => G.Adj v u)).card ≤ (s.erase v).card :=
    Finset.card_filter_le _ _
  have h2 : (s.erase v).card = s.card - 1 := Finset.card_erase_of_mem hv
  have h3 : s.card ≤ Fintype.card V := Finset.card_le_univ s
  omega

/-- **Five Colour Theorem (base case).**  Every planar graph on at most five
vertices is 5-colourable. -/
