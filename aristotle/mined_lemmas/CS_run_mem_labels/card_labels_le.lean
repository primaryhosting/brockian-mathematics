import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree for sorting 4 elements.  A `node i j l r`
compares the keys at positions `i` and `j`, continuing in `l` if the key at `i`
is smaller and in `r` otherwise.  A `leaf p` announces that the input ordering
is the permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by a decision tree. -/

theorem card_labels_le (t : DTree) : (labels t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [labels, depth]
  | node i j l r ihl ihr =>
      have h := Finset.card_union_le (labels l) (labels r)
      have hl : (labels l).card ≤ 2 ^ (max (depth l) (depth r)) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (labels r).card ≤ 2 ^ (max (depth l) (depth r)) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (labels (node i j l r)).card ≤ (labels l).card + (labels r).card := h
        _ ≤ 2 ^ (max (depth l) (depth r)) + 2 ^ (max (depth l) (depth r)) := by omega
        _ = 2 ^ depth (node i j l r) := by rw [depth, pow_succ]; ring

end DTree

/-- **Comparison-sort lower bound for 4 elements.**  Any comparison-based
decision tree that correctly determines the ordering of 4 elements (i.e. on the
input given by the permutation `σ` it outputs `σ`) must, in the worst case,
perform at least `⌈log₂ (4!)⌉ = 5` comparisons. -/
