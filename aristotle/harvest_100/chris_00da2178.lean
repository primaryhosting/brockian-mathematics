/-!
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Any comparison sort of 3 elements needs at least `⌈log₂ (3!)⌉ = 3` comparisons in the
worst case.

The development below is self-contained (core Lean 4 only, so that the required header
comment can be the first thing in the file, since Lean demands that `import` commands
precede every other command).

Model.  A comparison sort of three elements is modelled as a binary decision tree
(`DTree`): an internal node `cmp i j l r` compares the keys sitting at positions `i` and
`j` of the input and branches on the outcome, and a leaf `leaf q` reports the ordering
`q` it has determined.  An input is one of the `3! = 6` possible orderings of three
distinct keys (`Ord3`), `rank o i` being the rank of the key at position `i`.  The tree
sorts correctly when, on every input `o`, it reports exactly `o`.  `depth t` is the
worst-case number of comparisons the tree performs.
-/

namespace CS

/-- The `3! = 6` possible orderings of three distinct keys.  `xyz` means the key at
position `0` is the `x`-th smallest, etc. -/
inductive Ord3 where
  | abc | acb | bac | bca | cab | cba
  deriving DecidableEq, Repr

/-- `rank o i` is the rank (`0`, `1` or `2`) of the key sitting at position `i` when the
input ordering is `o`. -/
def rank (o : Ord3) (i : Nat) : Nat :=
  match o, i with
  | .abc, 0 => 0 | .abc, 1 => 1 | .abc, 2 => 2
  | .acb, 0 => 0 | .acb, 1 => 2 | .acb, 2 => 1
  | .bac, 0 => 1 | .bac, 1 => 0 | .bac, 2 => 2
  | .bca, 0 => 2 | .bca, 1 => 0 | .bca, 2 => 1
  | .cab, 0 => 1 | .cab, 1 => 2 | .cab, 2 => 0
  | .cba, 0 => 2 | .cba, 1 => 1 | .cba, 2 => 0
  | _, _ => 0

/-- A comparison-based decision tree on three keys. -/
inductive DTree where
  | leaf : Ord3 → DTree
  | cmp : Nat → Nat → DTree → DTree → DTree

/-- The worst-case number of comparisons performed by a decision tree. -/
def depth : DTree → Nat
  | .leaf _ => 0
  | .cmp _ _ l r => max (depth l) (depth r) + 1

/-- Running a decision tree on an input ordering. -/
def run : DTree → Ord3 → Ord3
  | .leaf q, _ => q
  | .cmp i j l r, o => if rank o i < rank o j then run l o else run r o

/-- The list of leaf labels of a decision tree, i.e. all its possible outputs. -/
def outputs : DTree → List Ord3
  | .leaf q => [q]
  | .cmp _ _ l r => outputs l ++ outputs r

/-- A binary tree of depth `d` has at most `2 ^ d` leaves. -/
theorem length_outputs_le (t : DTree) : (outputs t).length ≤ 2 ^ depth t := by
  induction t with
  | leaf q => simp [outputs, depth]
  | cmp i j l r ihl ihr =>
      have hl : (outputs l).length ≤ 2 ^ max (depth l) (depth r) :=
        Nat.le_trans ihl (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
      have hr : (outputs r).length ≤ 2 ^ max (depth l) (depth r) :=
        Nat.le_trans ihr (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
      have hpow : (2:Nat) ^ depth (DTree.cmp i j l r)
          = 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := by
        simp [depth, Nat.pow_succ]; omega
      simp only [outputs, List.length_append]
      omega

/-- Every result of a run is a leaf label of the tree. -/
theorem run_mem_outputs (t : DTree) (o : Ord3) : run t o ∈ outputs t := by
  induction t with
  | leaf q => simp [run, outputs]
  | cmp i j l r ihl ihr =>
      by_cases h : rank o i < rank o j <;> simp [run, outputs, h, ihl, ihr]

/-- Number of occurrences of `x` in a list of orderings. -/
def cnt (x : Ord3) : List Ord3 → Nat
  | [] => 0
  | y :: ys => (if x = y then 1 else 0) + cnt x ys

theorem cnt_pos_of_mem {x : Ord3} {L : List Ord3} (h : x ∈ L) : 1 ≤ cnt x L := by
  induction L with
  | nil => cases h
  | cons y ys ih =>
      cases List.mem_cons.mp h with
      | inl h' => subst h'; simp [cnt]
      | inr h' => have := ih h'; simp [cnt]; omega

/-- The length of a list of orderings is the sum of the multiplicities of the six
orderings. -/
theorem length_eq_cnt_sum (L : List Ord3) :
    L.length = cnt .abc L + cnt .acb L + cnt .bac L + cnt .bca L + cnt .cab L + cnt .cba L := by
  induction L with
  | nil => simp [cnt]
  | cons y ys ih => cases y <;> simp [cnt] <;> omega

/-- A correct comparison tree must have at least `3! = 6` leaves. -/
theorem six_le_length_outputs (t : DTree) (h : ∀ o : Ord3, run t o = o) :
    6 ≤ (outputs t).length := by
  have hmem : ∀ o : Ord3, o ∈ outputs t := by
    intro o
    have := run_mem_outputs t o
    rw [h o] at this
    exact this
  have h1 := cnt_pos_of_mem (hmem .abc)
  have h2 := cnt_pos_of_mem (hmem .acb)
  have h3 := cnt_pos_of_mem (hmem .bac)
  have h4 := cnt_pos_of_mem (hmem .bca)
  have h5 := cnt_pos_of_mem (hmem .cab)
  have h6 := cnt_pos_of_mem (hmem .cba)
  have := length_eq_cnt_sum (outputs t)
  omega

/-- The factorial function. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `IsCeilLog2 n k` says that `k = ⌈log₂ n⌉`: it is the least `k` with `n ≤ 2 ^ k`. -/
def IsCeilLog2 (n k : Nat) : Prop := n ≤ 2 ^ k ∧ ∀ j, n ≤ 2 ^ j → k ≤ j

theorem three_le_of_six_le_pow {d : Nat} (h : 6 ≤ 2 ^ d) : 3 ≤ d := by
  cases Nat.lt_or_ge d 3 with
  | inr hge => exact hge
  | inl hlt =>
      have hd : d ≤ 2 := by omega
      have : (2:Nat) ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hd
      omega

/-- `⌈log₂ (3!)⌉ = ⌈log₂ 6⌉ = 3`. -/
theorem ceilLog2_fact3 : IsCeilLog2 (fact 3) 3 :=
  ⟨by decide, fun _ hj => three_le_of_six_le_pow hj⟩

/-- **Comparison-sorting lower bound for three elements.**  Any comparison sort of `3`
elements — i.e. any comparison decision tree that correctly identifies each of the `3!`
input orderings — performs at least `⌈log₂ (3!)⌉ = 3` comparisons in the worst case.

The first conjunct states the bound for an arbitrary `k = ⌈log₂ (3!)⌉`, the second
records the numerical value `⌈log₂ (3!)⌉ = 3`, and the third is the resulting explicit
bound `depth t ≥ 3`. -/
theorem sorting_lb_3 (t : DTree) (h : ∀ o : Ord3, run t o = o) :
    (∀ k, IsCeilLog2 (fact 3) k → k ≤ depth t) ∧ IsCeilLog2 (fact 3) 3 ∧ 3 ≤ depth t := by
  have hsix : 6 ≤ 2 ^ depth t :=
    Nat.le_trans (six_le_length_outputs t h) (length_outputs_le t)
  have hfact : fact 3 ≤ 2 ^ depth t := hsix
  exact ⟨fun _ hk => hk.2 _ hfact, ceilLog2_fact3, three_le_of_six_le_pow hsix⟩

/-- An explicit correct comparison sort of three elements using three comparisons. -/
def sortTree3 : DTree :=
  .cmp 0 1
    (.cmp 1 2 (.leaf .abc) (.cmp 0 2 (.leaf .acb) (.leaf .cab)))
    (.cmp 0 2 (.leaf .bac) (.cmp 1 2 (.leaf .bca) (.leaf .cba)))

/-- The lower bound is tight: three comparisons suffice to sort three elements, so the
bound `⌈log₂ (3!)⌉ = 3` of `CS.sorting_lb_3` is attained (in particular the hypothesis of
`CS.sorting_lb_3` is satisfiable). -/
theorem sorting_ub_3 : (∀ o : Ord3, run sortTree3 o = o) ∧ depth sortTree3 = 3 := by
  refine ⟨fun o => ?_, rfl⟩
  cases o <;> rfl

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

