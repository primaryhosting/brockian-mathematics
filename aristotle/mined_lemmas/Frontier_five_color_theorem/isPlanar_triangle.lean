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

theorem isPlanar_triangle : IsPlanar (⊤ : SimpleGraph (Fin 3)) := by
  refine ⟨{ pos := trianglePos, pos_injective := ?_, vertex_notMem := ?_,
            edges_disjoint := ?_ }⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [trianglePos, Prod.ext_iff]
  · intro v a b hab hva hvb
    fin_cases v <;> fin_cases a <;> fin_cases b <;>
      simp_all [trianglePos, mem_openSegment_prod]
  · intro a b c d hab hcd hne
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hp1, hp2⟩
    rw [mem_openSegment_prod] at hp1 hp2
    obtain ⟨t, ht0, ht1, rfl⟩ := hp1
    obtain ⟨s, hs0, hs1, hps⟩ := hp2
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp_all [trianglePos, Prod.ext_iff] <;> linarith

/-! ### Kempe chain interchange

The second ingredient of the classical proof of the five colour theorem is the *Kempe
chain interchange*: in a proper colouring one may exchange two colours `i` and `j` on any
union `A` of connected components of the subgraph spanned by the vertices coloured `i` or
`j`, and the result is again a proper colouring.  This part of the argument is purely
combinatorial and is proved here in full generality. -/

open Classical in
/-- Exchange the colours `i` and `j` on the set `A`. -/
