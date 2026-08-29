-- (Lean requires `import` to be the first command of a file, so the header comment
-- follows it.)
import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
We formalise Dijkstra's algorithm on a finite directed graph whose edge weights are
nonnegative (encoded by taking values in `ℝ≥0∞`, where `⊤` means "no edge"), and prove
that it computes the true shortest-path distances from a fixed source.
-/

namespace CS

open scoped ENNReal

variable {V : Type*}

/-! ## Walks, their weights, and the shortest-path distance -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/

lemma gdist_triangle_edge (w : V → V → ℝ≥0∞) (s u v : V) :
    gdist w s v ≤ gdist w s u + w u v := by
  have hadd : gdist w s u + w u v
      = ⨅ b ∈ {x : ℝ≥0∞ | ∃ l : List V, endp s l = u ∧ wt w s l = x}, b + w u v :=
    ENNReal.sInf_add
  rw [hadd]
  refine le_iInf₂ ?_
  rintro x ⟨l, hl, rfl⟩
  have h : endp s (l ++ [v]) = v := by simp [endp_append, hl]
  calc gdist w s v ≤ wt w s (l ++ [v]) := gdist_le w h
    _ = wt w s l + w u v := by simp [wt_append, hl]

/-- Splitting a walk at its first vertex outside `S`. -/
