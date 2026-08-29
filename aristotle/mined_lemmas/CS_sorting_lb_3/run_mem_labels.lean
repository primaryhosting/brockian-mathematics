import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based sorting algorithm for `3` elements, presented as a (binary)
decision tree.  An internal node `node i j l r` asks the comparison "is the `i`-th
input element smaller than the `j`-th one?" and branches accordingly; a leaf
`leaf p` outputs the permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Running the decision tree on the input whose ranking is the permutation `σ`
(i.e. the `i`-th input element has rank `σ i`): each comparison `i` vs `j`
is answered by the truth value of `σ i < σ j`. -/

theorem run_mem_labels (t : DTree) (σ : Equiv.Perm (Fin 3)) : run t σ ∈ labels t := by
  induction t with
  | leaf p => simp [run, labels]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, labels, h, ihl, ihr]

end DTree

/-- A decision tree **sorts** if on every input it outputs the correct ranking. -/
