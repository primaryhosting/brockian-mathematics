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

universe u

namespace Frontier

/-- The Euclidean plane, in which planar graphs are drawn. -/
abbrev Plane : Type := ℝ × ℝ

/-- A *plane drawing* of a simple graph `G`: an injective placement of the vertices in the
plane together with, for every edge, an arc (a homeomorphic image of `[0,1]`) joining the
positions of its endpoints, such that arcs meet the vertex set only at their own endpoints and
two arcs belonging to distinct edges meet only at common endpoints. -/
structure Drawing {V : Type*} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  pos : V → Plane
  /-- Distinct vertices are drawn at distinct points. -/
  pos_injective : Function.Injective pos
  /-- The point set of the arc drawn for the (unordered) edge `{u, v}`. -/
  arc : V → V → Set Plane
  /-- The arc of an edge does not depend on the order of its endpoints. -/
  arc_symm : ∀ u v : V, arc u v = arc v u
  /-- The arc of an edge is a simple curve running from one endpoint to the other. -/
  arc_isArc : ∀ u v : V, G.Adj u v →
    ∃ f : ℝ → Plane, ContinuousOn f (Set.Icc 0 1) ∧ Set.InjOn f (Set.Icc 0 1) ∧
      f 0 = pos u ∧ f 1 = pos v ∧ arc u v = f '' Set.Icc 0 1
  /-- An arc passes through no vertices other than its own endpoints. -/
  arc_inter_pos : ∀ u v : V, G.Adj u v → ∀ w : V, pos w ∈ arc u v → w = u ∨ w = v
  /-- Two arcs belonging to distinct edges meet only at common endpoints. -/
  arc_inter_arc : ∀ u v x y : V, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
    ∀ p ∈ arc u v ∩ arc x y, ∃ w : V, (w = u ∨ w = v) ∧ (w = x ∨ w = y) ∧ p = pos w

/-- A graph is *planar* when it admits a plane drawing. -/

def Drawing.ofIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (D : Drawing G)
    (e : G ≃g H) : Drawing H where
  pos w := D.pos (e.symm w)
  pos_injective := by
    intro a b h
    simpa using congrArg e (D.pos_injective h)
  arc u v := D.arc (e.symm u) (e.symm v)
  arc_symm _ _ := D.arc_symm _ _
  arc_isArc _ _ h := D.arc_isArc _ _ (e.symm.map_adj_iff.mpr h)
  arc_inter_pos u v h w hw := by
    rcases D.arc_inter_pos _ _ (e.symm.map_adj_iff.mpr h) (e.symm w) hw with h1 | h1
    · exact Or.inl (by simpa using congrArg e h1)
    · exact Or.inr (by simpa using congrArg e h1)
  arc_inter_arc u v x y huv hxy hne p hp := by
    have hne' : s(e.symm u, e.symm v) ≠ s(e.symm x, e.symm y) := by
      intro h
      rw [Sym2.eq_iff] at h
      refine hne ?_
      rw [Sym2.eq_iff]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simpa using congrArg e h1, by simpa using congrArg e h2⟩
      · exact Or.inr ⟨by simpa using congrArg e h1, by simpa using congrArg e h2⟩
    obtain ⟨w, hw1, hw2, hw3⟩ := D.arc_inter_arc _ _ _ _ (e.symm.map_adj_iff.mpr huv)
      (e.symm.map_adj_iff.mpr hxy) hne' p hp
    refine ⟨e w, ?_, ?_, by simpa using hw3⟩
    · rcases hw1 with h | h
      · exact Or.inl (by simpa using congrArg e h)
      · exact Or.inr (by simpa using congrArg e h)
    · rcases hw2 with h | h
      · exact Or.inl (by simpa using congrArg e h)
      · exact Or.inr (by simpa using congrArg e h)

/-- Planarity is invariant under isomorphism of graphs. -/
