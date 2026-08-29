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

def cmpOracle {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → Bool :=
  fun i j => decide (σ i ≤ σ j)

/-- **Comparison-sort lower bound for 5 elements.**
If a comparison decision tree on 5 elements is correct, in the sense that its output
determines the input ordering (distinct orderings of the input yield distinct outputs),
then its worst-case number of comparisons is at least `⌈log₂ (5!)⌉ = 7`. -/
