import Mathlib
-- (Lean 4 requires `import` lines to precede any module docstring, so the requested
-- header comment appears immediately below the import.)

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

open SimpleGraph

/-! ## Planarity

We use the *straight-line* notion of planarity: a graph is planar when its vertices can be
placed at distinct points of the plane `ℝ × ℝ` in such a way that the closed segments
representing the edges meet only in common endpoints, and no vertex lies on a segment
representing an edge that is not incident to it.

By Fáry's theorem this is equivalent, for finite simple graphs, to the usual topological
notion of planarity (embeddability of the graph into the plane with arbitrary arcs as edges).
-/

/-- A straight-line planar drawing of `G`: an injective placement `p` of the vertices in the
plane such that (i) a vertex lying on the segment of an edge is an endpoint of that edge, and
(ii) the segments of two distinct edges meet only in common endpoints. -/

theorem colorable_four_of_maxDegree_le_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v : V, G.degree v ≤ 3) :
    G.Colorable 4 := by
  refine colorable_of_degenerate G 4 ?_
  rintro s ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  have hsub : s.filter (fun w => G.Adj v w) ⊆ G.neighborFinset v := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact (SimpleGraph.mem_neighborFinset G v w).2 hw.2
  have := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at this
  have := hdeg v
  omega

/-- Removing a vertex of degree at most three: this is the standard first reduction in the
proof of the Four Colour Theorem (a minimal counterexample has minimum degree at least
four).  If `G` minus the vertex `v` is 4-colourable and `v` has at most three neighbours,
then `G` itself is 4-colourable. -/
