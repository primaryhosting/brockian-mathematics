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
def run : DTree → Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then run l σ else run r σ

/-- The worst-case number of comparisons performed, i.e. the depth of the tree. -/
def depth : DTree → ℕ
  | leaf _ => 0
  | node _ _ l r => max (depth l) (depth r) + 1

/-- The (finite) set of answers appearing at the leaves of the tree. -/
def labels : DTree → Finset (Equiv.Perm (Fin 3))
  | leaf p => {p}
  | node _ _ l r => labels l ∪ labels r

/-- A tree of depth `d` has at most `2 ^ d` distinct leaf labels. -/
theorem card_labels_le_two_pow (t : DTree) : (labels t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [labels, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : (labels l).card ≤ 2 ^ (max (depth l) (depth r)) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (labels r).card ≤ 2 ^ (max (depth l) (depth r)) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (labels l).card + (labels r).card
          ≤ 2 ^ (max (depth l) (depth r)) + 2 ^ (max (depth l) (depth r)) :=
            Nat.add_le_add hl hr
        _ = 2 ^ depth (node i j l r) := by rw [depth, pow_succ]; ring

/-- Every output of the tree is one of its leaf labels. -/
theorem run_mem_labels (t : DTree) (σ : Equiv.Perm (Fin 3)) : run t σ ∈ labels t := by
  induction t with
  | leaf p => simp [run, labels]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, labels, h, ihl, ihr]

end DTree

/-- A decision tree **sorts** if on every input it outputs the correct ranking. -/
def Sorts (t : DTree) : Prop := ∀ σ : Equiv.Perm (Fin 3), t.run σ = σ

/-- **Comparison-sorting lower bound for 3 elements.**
Any comparison sort of `3` elements (modelled as a binary decision tree whose
internal nodes are comparisons between two of the inputs) must, in the worst case,
perform at least `⌈log₂ (3!)⌉ = 3` comparisons.

The proof is the classical information-theoretic argument: a tree of depth `d`
has at most `2 ^ d` leaves, but a correct algorithm must be able to output each of
the `3! = 6` permutations, so `6 ≤ 2 ^ d`, i.e. `d ≥ Nat.clog 2 6 = 3`. -/
theorem sorting_lb_3 (t : DTree) (ht : Sorts t) :
    Nat.clog 2 (Nat.factorial 3) ≤ t.depth := by
  -- every permutation occurs as a leaf label
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 3))) ⊆ t.labels := by
    intro σ _
    have := t.run_mem_labels σ
    rwa [ht σ] at this
  have hcard : Nat.factorial 3 ≤ (t.labels).card := by
    have h1 : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = Nat.factorial 3 := by
      simp [Finset.card_univ, Fintype.card_perm]
    calc Nat.factorial 3 = (Finset.univ : Finset (Equiv.Perm (Fin 3))).card := h1.symm
      _ ≤ (t.labels).card := Finset.card_le_card hsub
  have h2 : Nat.factorial 3 ≤ 2 ^ t.depth := hcard.trans t.card_labels_le_two_pow
  exact (Nat.pow_le_iff_le_clog (by norm_num)).mp h2

/-- The bound is the expected numeral: `⌈log₂ (3!)⌉ = 3`. -/
theorem clog_two_factorial_three : Nat.clog 2 (Nat.factorial 3) = 3 := by decide

/-- Restatement of `CS.sorting_lb_3` with the numeral: any correct comparison sort
of three elements needs at least three comparisons in the worst case. -/
theorem sorting_lb_3' (t : DTree) (ht : Sorts t) : 3 ≤ t.depth := by
  have := sorting_lb_3 t ht
  rwa [clog_two_factorial_three] at this

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

