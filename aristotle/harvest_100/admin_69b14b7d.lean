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
def run : DTree → Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then l.run σ else r.run σ

/-- The worst-case number of comparisons performed by the tree. -/
def depth : DTree → ℕ
  | leaf _ => 0
  | node _ _ l r => max l.depth r.depth + 1

/-- The (finite) set of outputs sitting at the leaves of the tree. -/
def leaves : DTree → Finset (Equiv.Perm (Fin 3))
  | leaf p => {p}
  | node _ _ l r => l.leaves ∪ r.leaves

/-- The tree is a *correct* sorting algorithm: on every input it outputs the
true ranking of that input. -/
def Sorts (t : DTree) : Prop := ∀ σ : Equiv.Perm (Fin 3), t.run σ = σ

/-- Every output of the tree is one of its leaf labels. -/
theorem run_mem_leaves (t : DTree) (σ : Equiv.Perm (Fin 3)) : t.run σ ∈ t.leaves := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, leaves, h, ihl, ihr]

/-- A binary tree of depth `d` has at most `2 ^ d` leaves. -/
theorem card_leaves_le (t : DTree) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine (Finset.card_union_le _ _).trans ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc l.leaves.card + r.leaves.card
          ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := by omega
        _ = 2 ^ (max l.depth r.depth + 1) := by ring
        _ = 2 ^ (node i j l r).depth := rfl

/-- A correct sorting tree must have at least `3! = 6` leaves: it realizes every
one of the `3!` possible rankings as an output. -/
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
theorem sorting_lb_3 (t : DTree) (h : t.Sorts) :
    Nat.clog 2 (Nat.factorial 3) ≤ t.depth := by
  have h1 : Nat.factorial 3 ≤ 2 ^ t.depth :=
    (t.card_leaves_factorial_le h).trans t.card_leaves_le
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 h1

/-- The bound above is literally `3` comparisons. -/
theorem clog_two_factorial_three : Nat.clog 2 (Nat.factorial 3) = 3 := by decide

/-- Restatement: any correct comparison sort of 3 elements needs at least 3
comparisons in the worst case. -/
theorem sorting_lb_3' (t : DTree) (h : t.Sorts) : 3 ≤ t.depth := by
  simpa [clog_two_factorial_three] using sorting_lb_3 t h

/-- An explicit correct comparison sort of 3 elements using 3 comparisons,
witnessing both that the model is non-vacuous and that the lower bound is
attained. -/
def sortTree3 : DTree :=
  .node 0 1
    (.node 1 2 (.leaf 1)
      (.node 0 2 (.leaf (Equiv.swap 1 2)) (.leaf (finRotate 3))))
    (.node 1 2
      (.node 0 2 (.leaf (Equiv.swap 0 1)) (.leaf (finRotate 3)⁻¹))
      (.leaf (Equiv.swap 0 2)))

theorem sortTree3_sorts : sortTree3.Sorts := by
  show ∀ σ : Equiv.Perm (Fin 3), sortTree3.run σ = σ
  decide

theorem sortTree3_depth : sortTree3.depth = 3 := by decide

/-- The bound of `⌈log₂ (3!)⌉ = 3` comparisons is tight. -/
theorem sorting_lb_3_tight : ∃ t : DTree, t.Sorts ∧ t.depth = 3 :=
  ⟨sortTree3, sortTree3_sorts, sortTree3_depth⟩

end CS

