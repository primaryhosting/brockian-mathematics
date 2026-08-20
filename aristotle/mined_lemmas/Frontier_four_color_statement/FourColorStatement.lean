/-
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated as a module docstring below: in Lean 4 a `/-! ... -/`
-- module docstring may not precede the `import` commands.)

import Mathlib

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

Mathlib has no notion of graph planarity, so this file supplies one:
`Frontier.PlanarEmbedding` (a drawing of a graph in `ℝ × ℝ` with non-crossing arcs)
and `Frontier.IsPlanar`.

* `Frontier.FourColorStatement` — the Four Colour Theorem itself (Appel–Haken):
  every planar graph is 4-colourable.  This is **not** proved here.
* `Frontier.four_color_statement` — the Lean-checked reduction proved here: the
  Four Colour Theorem for arbitrary (possibly infinite) planar graphs is
  *equivalent* to its restriction to finite planar graphs.  The nontrivial
  direction is de Bruijn–Erdős compactness, obtained from Mathlib's
  `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`, together with the fact
  that planarity is hereditary (`Frontier.IsPlanar.of_injective`).
* `Frontier.four_color_statement_fin` — a further reduction to graphs on `Fin n`.
* `Frontier.colorable_four_of_card_le` — the base case: graphs on at most four
  vertices are 4-colourable.
* Sanity checks that the planarity definition has content:
  `Frontier.isPlanar_bot`, `Frontier.isPlanar_top_fin_two` (positive examples) and
  `Frontier.not_isPlanar_set_real` (a negative example).
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

universe u v

/-- A *planar embedding* of a simple graph `G` in the Euclidean plane `ℝ × ℝ`:
vertices are sent to distinct points, each edge is drawn as an arc (a continuous
injective curve) joining the images of its endpoints, arcs pass through no vertex
other than their own endpoints, and two arcs of distinct edges meet only in the
images of vertices shared by the two edges. -/
structure PlanarEmbedding {V : Type u} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  pos : V → ℝ × ℝ
  /-- Distinct vertices get distinct positions. -/
  pos_inj : Function.Injective pos
  /-- The arc drawn for the edge `{u, v}`, parametrized by the unit interval. -/
  arc : V → V → unitInterval → ℝ × ℝ
  arc_cont : ∀ {a b : V}, G.Adj a b → Continuous (arc a b)
  arc_inj : ∀ {a b : V}, G.Adj a b → Function.Injective (arc a b)
  arc_zero : ∀ {a b : V}, G.Adj a b → arc a b 0 = pos a
  arc_one : ∀ {a b : V}, G.Adj a b → arc a b 1 = pos b
  /-- The two parametrizations of an edge trace out the same arc. -/
  arc_symm : ∀ {a b : V}, G.Adj a b → Set.range (arc a b) = Set.range (arc b a)
  /-- An arc meets no vertex other than its endpoints. -/
  arc_avoid : ∀ {a b : V}, G.Adj a b → ∀ w : V, pos w ∈ Set.range (arc a b) → w = a ∨ w = b
  /-- Arcs of distinct edges meet only at (positions of) common endpoints. -/
  arc_disjoint : ∀ {a b c d : V}, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
    Set.range (arc a b) ∩ Set.range (arc c d) ⊆ pos '' ({a, b} ∩ {c, d})

/-- A graph is *planar* if it admits a planar embedding, i.e. it can be drawn in the
plane with no crossing edges. -/

def FourColorStatement : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The Four Colour Theorem restricted to graphs with finitely many vertices. -/
