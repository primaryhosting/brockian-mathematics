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

theorem fourColorTheoremFinite_of_min_degree_four
    (h : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Planar G →
      (∀ v : V, 4 ≤ (G.neighborSet v).ncard) → G.Colorable 4) :
    FourColorTheoremFinite := by
  have key : ∀ n : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V ≤ n → Planar G → G.Colorable 4 := by
    intro n
    induction n with
    | zero =>
      intro V _ G hcard _
      have : IsEmpty V := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      exact SimpleGraph.Colorable.of_isEmpty 4
    | succ n ih =>
      intro V _ G hcard hplanar
      by_cases hdeg : ∃ v : V, (G.neighborSet v).ncard ≤ 3
      · obtain ⟨v, hv⟩ := hdeg
        have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
        have hcard' : Fintype.card ({v}ᶜ : Set V) ≤ n := by
          rw [Fintype.card_compl_set]
          simp only [Set.card_singleton]
          omega
        have hpl : Planar (G.induce ({v}ᶜ : Set V)) :=
          Planar.of_injective Subtype.val Subtype.val_injective (fun _ _ hab => hab) hplanar
        exact colorable_of_delete_small_degree_vertex G v hv (ih _ _ hcard' hpl)
      · push_neg at hdeg
        exact h V G hplanar (fun v => hdeg v)
  intro V _ G hplanar
  exact key (Fintype.card V) V G le_rfl hplanar

/-- **Reduction of the Four Colour Theorem to its finite case.**

If every finite planar graph is 4-colourable, then *every* planar graph (on a vertex set of
arbitrary cardinality) is 4-colourable. The proof is a compactness argument
(de Bruijn–Erdős): every finite subgraph of a planar graph is a finite planar graph. -/
