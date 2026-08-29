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

theorem planar_completeGraph_fin_two : Planar (⊤ : SimpleGraph (Fin 2)) := by
  have hfwd : ContinuousOn (fun t : ℝ => (t, (0 : ℝ))) (Set.Icc 0 1) := by fun_prop
  have hbwd : ContinuousOn (fun t : ℝ => ((1 - t : ℝ), (0 : ℝ))) (Set.Icc 0 1) := by fun_prop
  refine ⟨{ point := twoPoints
            point_injective := ?_
            arc := fun _ _ => unitSeg
            arc_symm := fun _ _ => rfl
            arc_isCurve := ?_
            arc_vertices := ?_
            arc_disjoint := ?_ }⟩
  · intro a b hab
    have : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := congrArg Prod.fst hab
    exact Fin.ext (by exact_mod_cast this)
  · intro u v huv
    have hne : u ≠ v := huv.ne
    fin_cases u <;> fin_cases v <;> simp_all
    · refine ⟨fun t => (t, 0), hfwd, ?_, by simp [twoPoints], by simp [twoPoints], rfl⟩
      intro a _ b _ hab
      simpa using congrArg Prod.fst hab
    · refine ⟨fun t => ((1 - t : ℝ), 0), hbwd, ?_, by norm_num [twoPoints],
        by norm_num [twoPoints], ?_⟩
      · intro a _ b _ hab
        have h := congrArg Prod.fst hab
        simp only at h
        linarith
      · ext p
        simp only [unitSeg, Set.mem_image, Set.mem_Icc]
        constructor
        · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨1 - t, ⟨by linarith, by linarith⟩, by simp⟩
        · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨1 - t, ⟨by linarith, by linarith⟩, by simp⟩
  · intro u v huv w _
    have hne : u ≠ v := huv.ne
    revert hne
    fin_cases u <;> fin_cases v <;> fin_cases w <;> simp
  · intro u v x y huv hxy hne
    exact absurd (by revert hne; fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;>
      simp_all [SimpleGraph.top_adj] : s(u, v) = s(x, y)) hne

/-! ### The statement of the Four Colour Theorem -/

/-- The Four Colour Theorem for *finite* planar graphs (with vertex type in `Type 0`). -/
