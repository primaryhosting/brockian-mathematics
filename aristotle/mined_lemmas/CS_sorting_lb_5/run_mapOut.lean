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

theorem run_mapOut {β : Type u} (f : α → β) (t : DTree n α) (o : Fin n → Fin n → Bool) :
    (t.mapOut f).run o = f (t.run o) := by
  induction t with
  | leaf a => rfl
  | node i j l r ihl ihr => by_cases h : o i j <;> simp [mapOut, run, h, ihl, ihr]

/-- The tree that simply performs, in order, all the comparisons in `ps`,
returning the list of answers. -/
