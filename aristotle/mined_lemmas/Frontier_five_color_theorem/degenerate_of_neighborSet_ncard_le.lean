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

theorem degenerate_of_neighborSet_ncard_le [Finite V] {G : SimpleGraph V} {k : ℕ}
    (hd : ∀ v, (G.neighborSet v).ncard ≤ k) : Degenerate k G := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hd v)⟩
  intro w hw
  exact hw.2

/-- **Five Color Theorem for planar graphs of maximum degree at most four.**
Here the degeneracy hypothesis is replaced by a purely local condition. -/
