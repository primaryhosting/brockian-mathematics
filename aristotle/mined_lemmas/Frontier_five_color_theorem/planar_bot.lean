/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Finset

variable {V : Type*}

/-! ## Planarity

Mathlib has no notion of planarity, so we introduce one.  For a *finite simple graph*,
planarity is equivalent (Fáry's theorem) to the existence of a **straight-line plane
drawing**: an injective placement `f : V → ℝ × ℝ` of the vertices such that the closed
segments representing the edges meet only in common endpoints, and no vertex lies on a
segment of an edge of which it is not an endpoint. -/

/-- `Planar G` says that `G` admits a straight-line plane drawing:
the vertices are placed injectively in the plane, the edges are drawn as straight segments,
no vertex lies on an edge it is not an endpoint of, and two distinct edges meet only at a
common endpoint. -/

theorem planar_bot (n : ℕ) : Planar (⊥ : SimpleGraph (Fin n)) := by
  refine ⟨fun i => ((i : ℝ), 0), ?_, ?_, ?_⟩
  · intro i j h
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Fin.ext h.1
  · intro a b v hab; exact absurd hab (by simp)
  · intro a b c d hab; exact absurd hab (by simp)

/-- The complete graph on two vertices (a single edge) is planar. -/
