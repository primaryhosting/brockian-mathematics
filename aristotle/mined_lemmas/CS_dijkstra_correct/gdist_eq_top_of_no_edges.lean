import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `wcost w u l` is the total weight of the walk that starts at `u` and visits the
vertices of `l` in order. -/

lemma gdist_eq_top_of_no_edges (s t : V) (h : s ≠ t) :
    gdist (fun _ _ => (⊤ : ℝ≥0∞)) s t = ⊤ := by
  rw [gdist, eq_top_iff]
  refine le_sInf ?_
  rintro c ⟨l, hl, rfl⟩
  cases l with
  | nil => exact absurd hl h
  | cons a l => simp [wcost]

/-! ### The invariant is maintained -/

omit [Fintype V] in
