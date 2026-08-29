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

theorem five_color_of_maxDegree_le_four [Fintype V] {G : SimpleGraph V}
    (hplanar : Planar G) (hd : ∀ v, (G.neighborSet v).ncard ≤ 4) : G.Colorable 5 :=
  five_color_theorem hplanar (degenerate_of_neighborSet_ncard_le hd)

/-- Sanity check: the hypotheses of `five_color_theorem` are simultaneously satisfiable by a
graph with an edge, so the theorem is not vacuous. -/
example : (⊤ : SimpleGraph (Fin 2)).Colorable 5 :=
  five_color_theorem planar_top_two (degenerate_of_card_le (by simp))

end Frontier

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

