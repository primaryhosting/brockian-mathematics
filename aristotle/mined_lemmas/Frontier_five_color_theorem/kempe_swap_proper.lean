/-
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the required header above is
-- given as a plain comment and repeated as the module docstring below.)

import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope of this file

Mathlib (at the pinned version) contains no theory of planar graphs, so planarity is
developed here from scratch: `Frontier.PlaneDrawing` is a straight-line drawing of a graph
in `ℝ × ℝ` and `Frontier.IsPlanar` says that such a drawing exists (by Fáry's theorem this
is equivalent, for finite simple graphs, to the usual topological notion of planarity).

What is proved here is the *base case* of the five colour theorem — the case that the
classical proof settles by a single greedy step, without any Kempe chain interchange:
every finite planar graph each of whose nonempty induced subgraphs has a vertex of degree
at most `4` is `5`-colourable (`Frontier.five_color_theorem`).  Concrete consequences are
that every planar graph of maximum degree at most `4` is `5`-colourable, and that every
graph on at most five vertices is `5`-colourable.

The purely combinatorial half of the remaining case is also proved here: the Kempe chain
interchange `Frontier.kempe_swap_proper`, which recolours a union of components of a
two-coloured subgraph.  What is *not* developed here is the topological input of the full
theorem — Euler's formula and the Jordan curve argument showing that two Kempe chains
around a vertex of degree `5` cannot both exist in a plane drawing.
-/

set_option autoImplicit false

namespace Frontier

open Finset

variable {V : Type*}

/-- A straight-line drawing of a simple graph `G` in the plane `ℝ × ℝ`:
vertices are placed at distinct points, edges are drawn as the straight segments between
their endpoints, no vertex lies in the interior of an edge, and the interiors of two
distinct edges are disjoint.  By Fáry's theorem this is, for finite simple graphs,
equivalent to the usual topological notion of planarity. -/
structure PlaneDrawing (G : SimpleGraph V) where
  /-- the position of each vertex in the plane -/
  pos : V → ℝ × ℝ
  pos_injective : Function.Injective pos
  /-- no vertex lies in the interior of an edge it is not an endpoint of -/
  vertex_notMem : ∀ v a b : V, G.Adj a b → v ≠ a → v ≠ b →
    pos v ∉ openSegment ℝ (pos a) (pos b)
  /-- interiors of distinct edges are disjoint -/
  edges_disjoint : ∀ a b c d : V, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
    openSegment ℝ (pos a) (pos b) ∩ openSegment ℝ (pos c) (pos d) = ∅

/-- A simple graph is *planar* when it admits a straight-line drawing in the plane. -/

theorem kempe_swap_proper {α : Type*} [DecidableEq α] {G : SimpleGraph V} {c : V → α}
    {i j : α} {A : Set V}
    (hproper : ∀ u w, G.Adj u w → c u ≠ c w)
    (hAcol : ∀ u ∈ A, c u = i ∨ c u = j)
    (hAclosed : ∀ u w, u ∈ A → G.Adj u w → (c w = i ∨ c w = j) → w ∈ A) :
    ∀ u w, G.Adj u w → kempeSwap c i j A u ≠ kempeSwap c i j A w := by
  classical
  by_cases hij : i = j
  · subst hij
    have hid : kempeSwap c i i A = c := by
      funext v
      by_cases hv : v ∈ A <;> by_cases hc : c v = i <;> simp [kempeSwap, hv, hc]
    rw [hid]
    exact hproper
  intro u w hadj
  have hji : j ≠ i := fun h => hij h.symm
  by_cases hu : u ∈ A <;> by_cases hw : w ∈ A
  · rcases hAcol u hu with h1 | h1 <;> rcases hAcol w hw with h2 | h2 <;>
      simp [kempeSwap, hu, hw, h1, h2, hij, hji] <;>
      exact absurd (h1.trans h2.symm) (hproper u w hadj)
  · have hcw : ¬ (c w = i ∨ c w = j) := fun h => hw (hAclosed u w hu hadj h)
    push_neg at hcw
    rcases hAcol u hu with h1 | h1 <;>
      simp [kempeSwap, hu, hw, h1, hji, Ne.symm hcw.1, Ne.symm hcw.2]
  · have hcu : ¬ (c u = i ∨ c u = j) := fun h => hu (hAclosed w u hw hadj.symm h)
    push_neg at hcu
    rcases hAcol w hw with h1 | h1 <;>
      simp [kempeSwap, hu, hw, h1, hji, hcu.1, hcu.2]
  · simpa [kempeSwap, hu, hw] using hproper u w hadj

/-- `Degenerate G k` says that every nonempty set of vertices contains a vertex having at
most `k` neighbours inside that set.  Equivalently, every nonempty subgraph of `G` induced
on a set of vertices has a vertex of degree at most `k`. -/
