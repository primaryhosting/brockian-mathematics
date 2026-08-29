/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree for sorting `5` elements.
A `node i j l r` compares the elements at positions `i` and `j`, continuing in `l`
if the `i`-th one is smaller and in `r` otherwise; a `leaf p` outputs the
permutation `p`. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 5) → DTree
  | node : Fin 5 → Fin 5 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/
def depth : DTree → ℕ
  | .leaf _ => 0
  | .node _ _ l r => max l.depth r.depth + 1

/-- Running the tree on the input whose ranking is given by the permutation `σ`
(so the element at position `i` has rank `σ i`). -/
def eval : DTree → Equiv.Perm (Fin 5) → Equiv.Perm (Fin 5)
  | .leaf p, _ => p
  | .node i j l r, σ => if σ i < σ j then l.eval σ else r.eval σ

/-- The set of permutations appearing as labels of leaves. -/
def leaves : DTree → Finset (Equiv.Perm (Fin 5))
  | .leaf p => {p}
  | .node _ _ l r => l.leaves ∪ r.leaves

theorem eval_mem_leaves (t : DTree) (σ : Equiv.Perm (Fin 5)) : t.eval σ ∈ t.leaves := by
  induction t with
  | leaf p => simp [eval, leaves]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [eval, leaves, h, ihl, ihr]

theorem card_leaves_le (t : DTree) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine (Finset.card_union_le _ _).trans ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc l.leaves.card + r.leaves.card ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) :=
            Nat.add_le_add hl hr
        _ = 2 ^ (max l.depth r.depth + 1) := by ring
        _ = 2 ^ (node i j l r).depth := rfl

/-- A decision tree *sorts* if on every input it outputs the correct ranking. -/
def Sorts (t : DTree) : Prop := ∀ σ : Equiv.Perm (Fin 5), t.eval σ = σ

end DTree

/-- `⌈log₂(5!)⌉ = 7`. -/
theorem clog_two_factorial_five : Nat.clog 2 (Nat.factorial 5) = 7 := by
  have h : Nat.factorial 5 = 120 := by decide
  rw [h]
  have h1 : Nat.clog 2 120 ≤ 7 := (Nat.clog_le_iff_le_pow (by norm_num)).2 (by norm_num)
  have h2 : 6 < Nat.clog 2 120 := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by norm_num)
  omega

/-- **Comparison-sorting lower bound for 5 elements.**
Any comparison-based decision tree that correctly sorts `5` elements has worst-case
depth at least `⌈log₂(5!)⌉ = 7`. -/
theorem sorting_lb_5 (t : DTree) (ht : t.Sorts) :
    Nat.clog 2 (Nat.factorial 5) ≤ t.depth ∧ 7 ≤ t.depth := by
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 5))) ⊆ t.leaves := by
    intro σ _
    have := t.eval_mem_leaves σ
    rwa [ht σ] at this
  have hcard : (120 : ℕ) ≤ t.leaves.card := by
    have := Finset.card_le_card hsub
    simpa using this
  have hpow : (120 : ℕ) ≤ 2 ^ t.depth := hcard.trans t.card_leaves_le
  have h7 : Nat.clog 2 120 ≤ t.depth := (Nat.clog_le_iff_le_pow (by norm_num)).2 hpow
  have hfac : Nat.factorial 5 = 120 := by decide
  refine ⟨by rw [hfac]; exact h7, ?_⟩
  have : Nat.clog 2 120 = 7 := by rw [← hfac]; exact clog_two_factorial_five
  omega

/-- The real-logarithm form of the bound: `⌈log₂(5!)⌉ = 7`. -/
theorem ceil_logb_two_factorial_five : ⌈Real.logb 2 (Nat.factorial 5)⌉ = 7 := by
  have hfac : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hfac]
  have h1 : Real.logb 2 120 ≤ 7 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num),
      show ((7 : ℝ)) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h2 : (6 : ℝ) < Real.logb 2 120 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num),
      show ((6 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hle : ⌈Real.logb 2 120⌉ ≤ 7 :=
    Int.ceil_le.2 (by exact_mod_cast h1 : Real.logb 2 120 ≤ ((7 : ℤ) : ℝ))
  have hlt : (6 : ℤ) < ⌈Real.logb 2 120⌉ :=
    Int.lt_ceil.2 (by exact_mod_cast h2 : ((6 : ℤ) : ℝ) < Real.logb 2 120)
  omega

/-- **Comparison-sorting lower bound for 5 elements, real-logarithm form.**
Any correct comparison-based sorting decision tree for `5` elements makes at least
`⌈log₂(5!)⌉` comparisons in the worst case. -/
theorem sorting_lb_5_logb (t : DTree) (ht : t.Sorts) :
    ⌈Real.logb 2 (Nat.factorial 5)⌉ ≤ (t.depth : ℤ) := by
  rw [ceil_logb_two_factorial_five]
  exact_mod_cast (sorting_lb_5 t ht).2

end CS

#print axioms CS.sorting_lb_5
#print axioms CS.sorting_lb_5_logb

import RequestProject.SortingLb5
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

