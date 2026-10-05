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

theorem run_mem_outs (t : DTree n α) (o : Fin n → Fin n → Bool) : t.run o ∈ t.outs := by
  induction t with
  | leaf a => simp [run, outs]
  | node i j l r ihl ihr =>
      by_cases h : o i j <;> simp [run, outs, h, ihl, ihr]

/-- A tree of depth `d` has at most `2 ^ d` leaves. -/
