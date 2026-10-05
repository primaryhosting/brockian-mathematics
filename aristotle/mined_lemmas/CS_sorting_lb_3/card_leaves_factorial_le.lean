/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/`: a module docstring is a
-- command and Lean 4 does not permit it before the `import` line.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-! ## The comparison-sort decision-tree model on 3 elements

An input to a comparison sort on 3 distinct keys is described, up to order
isomorphism, by the permutation `σ : Equiv.Perm (Fin 3)` giving the *rank*
`σ i` of the key stored at position `i`.

A deterministic comparison sort is a binary decision tree: each internal node
compares the keys at two positions `i` and `j` (the only information the
algorithm may extract from the input), and branches on the outcome; each leaf
outputs a permutation, the claimed ranking of the input. -/

/-- A comparison-based decision tree for sorting 3 elements. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- Running the decision tree on the input whose ranking is `σ`: the comparison
at a node `node i j l r` asks whether the key at position `i` is smaller than
the key at position `j`, i.e. whether `σ i < σ j`. -/

theorem card_leaves_factorial_le (t : DTree) (h : t.Sorts) :
    Nat.factorial 3 ≤ t.leaves.card := by
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 3))) ⊆ t.leaves := by
    intro σ _
    have := t.run_mem_leaves σ
    rwa [h σ] at this
  have hcard := Finset.card_le_card hsub
  have : Fintype.card (Equiv.Perm (Fin 3)) = Nat.factorial 3 := by
    simp [Fintype.card_perm]
  simpa [Finset.card_univ, this] using hcard

end DTree

/-- **Comparison-sort lower bound for 3 elements.**
Any correct comparison-based sorting algorithm for 3 elements (modelled as a
binary decision tree whose internal nodes compare two positions of the input)
performs at least `⌈log₂ (3!)⌉ = 3` comparisons in the worst case. -/
