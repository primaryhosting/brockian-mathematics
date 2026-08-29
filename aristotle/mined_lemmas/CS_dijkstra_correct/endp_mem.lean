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

lemma endp_mem (s : V) {l : List V} (hl : l ≠ []) : endp s l ∈ l := by
  induction l generalizing s with
  | nil => exact absurd rfl hl
  | cons a t ih =>
      rcases eq_or_ne t [] with rfl | ht
      · simp
      · exact List.mem_cons_of_mem _ (ih a ht)

/-- Any walk gives an upper bound for the distance. -/
