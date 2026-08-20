/-
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

universe u v

/-!
## Planarity

Mathlib (at the pinned commit) contains no theory of planar graphs, so we formalize
planarity from scratch, topologically: a *plane drawing* of a simple graph `G` consists of

* an injective placement `vert : V → ℝ × ℝ` of the vertices in the plane;
* for every edge `e` of `G` an arc, i.e. a continuous injective path
  `path e : [0,1] → ℝ × ℝ`, whose two endpoints are exactly the placements of the two
  endpoints of `e`;

subject to the two conditions that make the drawing *plane* (crossing-free):

* an arc meets the set of placed vertices only in its own endpoints;
* two distinct arcs meet only in placements of vertices common to both edges.
-/

/-- The set of endpoints of an edge `e`, as a subset of the vertex type. -/

theorem isPlanar_top_bool : IsPlanar (⊤ : SimpleGraph Bool) := by
  have hedge : ∀ e : (⊤ : SimpleGraph Bool).edgeSet, (e : Sym2 Bool) = s(false, true) := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at he
      cases a <;> cases b <;> simp_all [Sym2.eq_swap]
  have hends : ∀ e : (⊤ : SimpleGraph Bool).edgeSet,
      endpoints (e : Sym2 Bool) = Set.univ := by
    intro e; rw [hedge e]; ext x; cases x <;> simp [endpoints]
  have hvert : ((fun b : Bool => ((if b then (1:ℝ) else 0), (0:ℝ))) '' Set.univ)
      = {((0:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))} := by
    ext x
    constructor
    · rintro ⟨b, -, rfl⟩; cases b <;> simp
    · rintro (rfl | rfl)
      · exact ⟨false, trivial, by simp⟩
      · exact ⟨true, trivial, by simp⟩
  refine ⟨{ vert := fun b => ((if b then (1:ℝ) else 0), 0)
            vert_inj := ?_
            path := fun _ t => (t, 0)
            path_cont := ?_
            path_inj := ?_
            path_ends := ?_
            arc_meets_vert := ?_
            arc_disjoint := ?_ }⟩
  · intro a b hab; cases a <;> cases b <;> simp_all
  · intro e; fun_prop
  · intro e t _ s _ h; simpa using congrArg Prod.fst h
  · intro e; rw [hends e, hvert]
  · intro e
    rw [hends e, hvert]
    refine subset_trans Set.inter_subset_right ?_
    rintro x ⟨b, rfl⟩; cases b <;> simp
  · intro e f hne
    exact absurd (Subtype.ext ((hedge e).trans (hedge f).symm)) hne

/-!
## The Four Colour Theorem

`FourColorConjecture` is the statement of the Appel–Haken theorem: every planar simple
graph (on an arbitrary, possibly infinite, vertex type) has a proper colouring with four
colours.  `FourColorConjectureFinite` is its restriction to finite graphs.

These are `Prop`-valued definitions; we do *not* assert them.  What is proved below,
`four_color_statement`, is the reduction of the general statement to the finite case.
-/

/-- The Four Colour Theorem: every planar simple graph is 4-colourable. -/
