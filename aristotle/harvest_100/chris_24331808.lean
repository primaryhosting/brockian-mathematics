/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary decision
tree.  A `node i j l r` compares the input values at positions `i` and `j` and branches
accordingly; a `leaf σ` outputs the permutation `σ`. -/
inductive DecTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → DecTree n
  | node : Fin n → Fin n → DecTree n → DecTree n → DecTree n

namespace DecTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the algorithm, i.e. the height of the
decision tree. -/
def depth : DecTree n → ℕ
  | leaf _ => 0
  | node _ _ l r => max (depth l) (depth r) + 1

/-- Running the algorithm on the input whose ranking is given by the permutation `τ`
(the element at position `i` has rank `τ i`).  Each comparison node asks whether the value
at position `i` is smaller than the value at position `j`, i.e. whether `τ i < τ j`. -/
def run : DecTree n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | leaf σ, _ => σ
  | node i j l r, τ => if τ i < τ j then run l τ else run r τ

/-- The set of possible outputs of the algorithm (the labels of the leaves). -/
def labels : DecTree n → Finset (Equiv.Perm (Fin n))
  | leaf σ => {σ}
  | node _ _ l r => labels l ∪ labels r

/-- Every output of the algorithm is the label of one of its leaves. -/
theorem run_mem_labels (t : DecTree n) (τ : Equiv.Perm (Fin n)) : run t τ ∈ labels t := by
  induction t with
  | leaf σ => simp [run, labels]
  | node i j l r ihl ihr =>
      by_cases h : τ i < τ j <;> simp [run, labels, h, ihl, ihr]

/-- A binary decision tree of height `d` has at most `2 ^ d` distinct leaf labels. -/
theorem card_labels_le (t : DecTree n) : (labels t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf σ => simp [labels, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : (labels l).card ≤ 2 ^ max (depth l) (depth r) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (labels r).card ≤ 2 ^ max (depth l) (depth r) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (labels l).card + (labels r).card
          ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := by omega
        _ = 2 ^ depth (node i j l r) := by simp [depth, pow_succ]; ring

end DecTree

/-- A comparison sort is *correct* if on every input it outputs the ranking permutation of
that input. -/
def Correct {n : ℕ} (t : DecTree n) : Prop := ∀ τ : Equiv.Perm (Fin n), t.run τ = τ

/-- A correct comparison sort on `n` elements must be able to output all `n!` permutations,
hence has at least `n!` leaves. -/
theorem factorial_le_card_labels {n : ℕ} (t : DecTree n) (h : Correct t) :
    n ! ≤ (t.labels).card := by
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ t.labels := by
    intro τ _
    have := t.run_mem_labels τ
    rwa [h τ] at this
  have := Finset.card_le_card hsub
  simpa [Fintype.card_perm] using this

/-- **Comparison-sorting lower bound for 3 elements.**  Any correct comparison sort on
3 elements performs at least `⌈log₂ (3!)⌉ = 3` comparisons in the worst case. -/
theorem sorting_lb_3 (t : DecTree 3) (h : Correct t) :
    Nat.clog 2 (3 !) ≤ t.depth ∧ 3 ≤ t.depth := by
  have h6 : (3 : ℕ)! ≤ 2 ^ t.depth :=
    (factorial_le_card_labels t h).trans (DecTree.card_labels_le t)
  have hclog : Nat.clog 2 (3 !) ≤ t.depth :=
    (Nat.clog_le_iff_le_pow (b := 2) (by norm_num)).2 h6
  refine ⟨hclog, ?_⟩
  by_contra hlt
  push_neg at hlt
  interval_cases hd : t.depth

/-- An explicit correct comparison sort on 3 elements using 3 comparisons in the worst case:
this shows the hypothesis of `CS.sorting_lb_3` is satisfiable and that the bound is tight. -/
def sorter3 : DecTree 3 :=
  .node 0 1
    (.node 1 2 (.leaf 1) (.node 0 2 (.leaf (Equiv.swap 1 2)) (.leaf (finRotate 3))))
    (.node 0 2 (.leaf (Equiv.swap 0 1))
      (.node 1 2 (.leaf (finRotate 3)⁻¹) (.leaf (Equiv.swap 0 2))))

/-- The bound of `CS.sorting_lb_3` is attained: there is a correct comparison sort on
3 elements of worst-case cost exactly `⌈log₂ (3!)⌉ = 3`. -/
theorem exists_correct_sorter_depth_three :
    ∃ t : DecTree 3, Correct t ∧ t.depth = 3 := by
  refine ⟨sorter3, ?_, ?_⟩
  · unfold Correct sorter3; decide
  · unfold sorter3 DecTree.depth; decide

end CS

