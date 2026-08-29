import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

namespace Frontier

universe u

variable {V : Type u}

/-! ## Plane straight-line drawings

Mathlib (at the pinned commit) contains no theory of planar graphs at all, so we
first have to say what "planar" means.

We use the *straight-line* (Fáry) formulation: a finite simple graph is planar
exactly when it can be drawn in the plane with vertices at distinct points and
edges drawn as straight segments which meet only at shared endpoints.  By
Fáry's theorem this is equivalent to the usual topological definition for
finite simple graphs, and it has the advantage of being completely elementary
to state. -/

/-- The open straight segment in `ℝ²` drawn for an (unordered) edge `e`, when the
vertices are placed by `p`. -/

theorem isPlanar_top_fin_two : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  classical
  have hedge : ∀ e ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet, e = s(0, 1) := by
    intro e he
    induction e with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      have hab : a ≠ b := he.ne
      fin_cases a <;> fin_cases b <;> simp_all [Sym2.eq_swap]
  have hne : (![((0:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] : Fin 2 → ℝ × ℝ) 0
      ≠ (![((0:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] : Fin 2 → ℝ × ℝ) 1 := by
    simp [Prod.ext_iff]
  refine ⟨![((0:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))], ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Prod.ext_iff]
  · intro e he f hf hef
    exact absurd ((hedge e he).trans (hedge f hf).symm) hef
  · intro v e he
    rw [hedge e he, seg_mk]
    fin_cases v
    · exact fun hh => hne (left_mem_openSegment_iff.mp hh)
    · exact fun hh => hne (right_mem_openSegment_iff.mp hh)

/-! ## Degeneracy and greedy colouring

The inductive engine behind the Five Colour Theorem: if every nonempty set of
vertices contains a vertex with at most `k` neighbours inside the set, then `G`
is `(k+1)`-colourable. -/

/-- `G` is `k`-degenerate: every nonempty finite set of vertices contains a vertex
with at most `k` neighbours inside the set. -/
