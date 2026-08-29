/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is a
-- plain block comment and is repeated below as the module docstring.)
import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based decision tree for sorting three elements.
A `node i j l r` compares the elements sitting at positions `i` and `j` of the input and
branches accordingly; a `leaf p` outputs the permutation `p`. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree
  deriving DecidableEq

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/
def depth : DTree → ℕ
  | leaf _ => 0
  | node _ _ l r => 1 + max (depth l) (depth r)

/-- The set of permutations that the tree can output. -/
def leaves : DTree → Finset (Equiv.Perm (Fin 3))
  | leaf p => {p}
  | node _ _ l r => leaves l ∪ leaves r

/-- Running the tree on an input whose element at position `i` has rank `σ i`. -/
def run : DTree → Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then run l σ else run r σ

/-- The output of a run is always one of the leaf labels. -/
lemma run_mem_leaves (t : DTree) (σ : Equiv.Perm (Fin 3)) : run t σ ∈ leaves t := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, leaves, h, ihl, ihr]

/-- A binary tree of depth `d` has at most `2 ^ d` distinct leaf labels. -/
lemma card_leaves_le (t : DTree) : (leaves t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      have h : (leaves (node i j l r)).card ≤ (leaves l).card + (leaves r).card :=
        Finset.card_union_le _ _
      have hl : (leaves l).card ≤ 2 ^ max (depth l) (depth r) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (leaves r).card ≤ 2 ^ max (depth l) (depth r) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (leaves (node i j l r)).card ≤ (leaves l).card + (leaves r).card := h
        _ ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := by omega
        _ = 2 ^ (1 + max (depth l) (depth r)) := by ring
        _ = 2 ^ depth (node i j l r) := by rw [depth]

end DTree

/-- **Comparison-sorting lower bound for 3 elements.**
Any comparison-based decision tree that correctly sorts every input of three distinct
elements (i.e. outputs the true ranking permutation `σ` on every input `σ`) must perform
at least `⌈log₂ 3!⌉ = 3` comparisons in the worst case. -/
theorem sorting_lb_3 (t : DTree) (hcorrect : ∀ σ : Equiv.Perm (Fin 3), t.run σ = σ) :
    Nat.clog 2 (Nat.factorial 3) ≤ t.depth := by
  have hall : (Finset.univ : Finset (Equiv.Perm (Fin 3))) ⊆ t.leaves := by
    intro σ _
    have := t.run_mem_leaves σ
    rwa [hcorrect σ] at this
  have hcard : Nat.factorial 3 ≤ (t.leaves).card := by
    have h1 : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card ≤ (t.leaves).card :=
      Finset.card_le_card hall
    simpa [Nat.factorial] using h1
  have h2 : Nat.factorial 3 ≤ 2 ^ t.depth := hcard.trans (DTree.card_leaves_le t)
  exact Nat.clog_le_of_le_pow h2

/-- The bound is exactly `3`. -/
theorem clog_two_factorial_three : Nat.clog 2 (Nat.factorial 3) = 3 := by decide

/-- An explicit comparison-sorting decision tree for three elements, using 3 comparisons. -/
def sortTree3 : DTree :=
  .node 0 1
    (.node 1 2
      (.leaf 1)
      (.node 0 2
        (.leaf (Equiv.swap 1 2))
        (.leaf (Equiv.swap 0 1 * Equiv.swap 1 2))))
    (.node 0 2
      (.leaf (Equiv.swap 0 1))
      (.node 1 2
        (.leaf (Equiv.swap 1 2 * Equiv.swap 0 1))
        (.leaf (Equiv.swap 0 2))))

/-- The tree `sortTree3` sorts correctly. -/
theorem sortTree3_correct (σ : Equiv.Perm (Fin 3)) : sortTree3.run σ = σ := by
  revert σ
  decide

/-- The tree `sortTree3` uses exactly 3 comparisons in the worst case. -/
theorem sortTree3_depth : sortTree3.depth = 3 := by decide

/-- The lower bound of `⌈log₂ 3!⌉ = 3` comparisons is attained, hence tight. -/
theorem sorting_lb_3_tight :
    ∃ t : DTree, (∀ σ : Equiv.Perm (Fin 3), t.run σ = σ) ∧
      t.depth = Nat.clog 2 (Nat.factorial 3) :=
  ⟨sortTree3, sortTree3_correct, by rw [sortTree3_depth, clog_two_factorial_three]⟩

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

