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

def labels : DTree → Finset (Equiv.Perm (Fin 3))
  | leaf p => {p}
  | node _ _ l r => labels l ∪ labels r

/-- A tree of depth `d` has at most `2 ^ d` distinct leaf labels. -/
