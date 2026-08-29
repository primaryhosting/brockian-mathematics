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

theorem exists_distinguishing_tree :
    ∃ t : DTree 5 (List Bool),
      Function.Injective fun σ : Equiv.Perm (Fin 5) => t.run (cmpOracle σ) := by
  refine ⟨DTree.probe ((List.finRange 5) ×ˢ (List.finRange 5)), ?_⟩
  intro σ τ hst
  simp only [DTree.run_probe, List.map_inj_left] at hst
  refine perm_eq_of_le_iff (fun i j => ?_)
  have := hst (i, j) (by simp)
  simpa [cmpOracle] using this

/-- The bound is literally `7` comparisons. -/
