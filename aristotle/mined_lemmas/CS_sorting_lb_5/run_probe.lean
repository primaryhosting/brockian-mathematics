import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

/-- A comparison-based decision tree on `n` elements with results in `α`.
An internal node compares the elements at two positions and branches on the answer. -/
inductive DTree (n : ℕ) (α : Type u) where
  | leaf : α → DTree n α
  | node : Fin n → Fin n → DTree n α → DTree n α → DTree n α

namespace DTree

variable {n : ℕ} {α : Type u}

/-- Worst-case number of comparisons performed by the tree. -/

theorem run_probe (ps : List (Fin n × Fin n)) (o : Fin n → Fin n → Bool) :
    (probe ps).run o = ps.map (fun p => o p.1 p.2) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : o p.1 p.2 <;> simp [probe, run, run_mapOut, h, ih]

end DTree

/-- The comparison oracle induced by an ordering `σ` of the `n` input positions:
the answer to "is the element at position `i` at most the element at position `j`?". -/
