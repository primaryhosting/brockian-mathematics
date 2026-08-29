/-
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede every command, including module docstrings, so the
-- header above is repeated verbatim as the module docstring immediately after the import.)

import Mathlib

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

universe u v

/-- The Euclidean plane, in which planar graphs are drawn. -/
abbrev Plane : Type := ℝ × ℝ

/-- A (topological) planar embedding of a simple graph `G`: an injective placement of the
vertices in the plane together with, for every edge, an arc (the homeomorphic image of a
closed interval) joining its endpoints, such that

* no arc passes through a vertex other than its own endpoints, and
* two arcs belonging to distinct edges meet only in common endpoints.

This is the standard definition of a plane drawing of a graph. -/
structure PlanarEmbedding {V : Type u} (G : SimpleGraph V) where
  /-- The position of each vertex in the plane. -/
  point : V → Plane
  /-- Distinct vertices get distinct positions. -/
  point_injective : Function.Injective point
  /-- The arc drawn for the (unordered) pair `{u, v}`; only constrained when `u` and `v`
  are adjacent. -/
  arc : V → V → Set Plane
  /-- The arc only depends on the unordered pair. -/
  arc_symm : ∀ u v, arc u v = arc v u
  /-- For an edge `uv` the set `arc u v` is a simple curve from `point u` to `point v`. -/
  arc_isCurve : ∀ ⦃u v : V⦄, G.Adj u v → ∃ f : ℝ → Plane,
    ContinuousOn f (Set.Icc 0 1) ∧ Set.InjOn f (Set.Icc 0 1) ∧
      f 0 = point u ∧ f 1 = point v ∧ f '' Set.Icc 0 1 = arc u v
  /-- An arc contains no vertex other than its endpoints. -/
  arc_vertices : ∀ ⦃u v : V⦄, G.Adj u v → ∀ w : V, point w ∈ arc u v → w = u ∨ w = v
  /-- Arcs of distinct edges meet only at shared endpoints. -/
  arc_disjoint : ∀ ⦃u v x y : V⦄, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
    arc u v ∩ arc x y ⊆ point '' (({u, v} : Set V) ∩ ({x, y} : Set V))

/-- A simple graph is *planar* when it admits a plane drawing. -/

theorem colorable_of_delete_small_degree_vertex {V : Type u} [Finite V] (G : SimpleGraph V)
    (v : V) (hdeg : (G.neighborSet v).ncard ≤ 3)
    (h : (G.induce ({v}ᶜ : Set V)).Colorable 4) : G.Colorable 4 := by
  obtain ⟨C⟩ := h
  classical
  set c' : V → Fin 4 := fun w => if hw : w = v then 0 else C ⟨w, by simpa using hw⟩ with hc'
  set S : Set (Fin 4) := c' '' (G.neighborSet v) with hS
  have hfin : (G.neighborSet v).Finite := Set.toFinite _
  have hScard : S.ncard ≤ 3 := le_trans (Set.ncard_image_le hfin) hdeg
  have hz : ∃ z : Fin 4, z ∉ S := by
    by_contra hcon
    push_neg at hcon
    have huniv : S = Set.univ := Set.eq_univ_iff_forall.mpr hcon
    rw [huniv, Set.ncard_univ] at hScard
    simp at hScard
  obtain ⟨z, hzS⟩ := hz
  refine ⟨SimpleGraph.Coloring.mk (fun w => if w = v then z else c' w) ?_⟩
  intro a b hab
  by_cases ha : a = v
  · subst ha
    have hb : b ≠ a := (hab.ne).symm
    simp only [if_neg hb]
    intro hEq
    exact hzS ⟨b, hab, hEq.symm⟩
  · by_cases hb : b = v
    · subst hb
      simp only [if_neg ha]
      intro hEq
      exact hzS ⟨a, hab.symm, hEq⟩
    · simp only [if_neg ha, if_neg hb, hc', dif_neg ha, dif_neg hb]
      exact C.valid (by simpa using hab)

/-- **Reduction of the finite Four Colour Theorem to graphs of minimum degree at least four.**

A smallest counterexample has no vertex of degree `≤ 3`, since such a vertex can be deleted and
its colour restored. Hence it suffices to prove the theorem for finite planar graphs in which
every vertex has at least four neighbours. -/
