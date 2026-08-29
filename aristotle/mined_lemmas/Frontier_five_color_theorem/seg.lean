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

noncomputable def seg (p : V → ℝ × ℝ) (e : Sym2 V) : Set (ℝ × ℝ) :=
  Sym2.lift ⟨fun a b => openSegment ℝ (p a) (p b), fun a b => openSegment_symm ℝ (p a) (p b)⟩ e

@[simp]
