/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based sorting algorithm for 3 elements, modelled as a decision tree.
An internal node `cmp i j yes no` compares the entries at positions `i` and `j` of the
input, and branches to `yes` if `x i ≤ x j` and to `no` otherwise.  A leaf is labelled
by the permutation the algorithm outputs. -/
inductive CTree where
  | leaf : Equiv.Perm (Fin 3) → CTree
  | cmp : Fin 3 → Fin 3 → CTree → CTree → CTree
  deriving Inhabited

namespace CTree

/-- The result of running the decision tree on the input `x`. -/
def run : CTree → (Fin 3 → ℕ) → Equiv.Perm (Fin 3)
  | leaf p, _ => p
  | cmp i j yes no, x => if x i ≤ x j then run yes x else run no x

/-- The worst-case number of comparisons performed by the tree. -/
def depth : CTree → ℕ
  | leaf _ => 0
  | cmp _ _ yes no => max (depth yes) (depth no) + 1

/-- The set of permutations the tree can possibly output. -/
def reachable : CTree → Finset (Equiv.Perm (Fin 3))
  | leaf p => {p}
  | cmp _ _ yes no => reachable yes ∪ reachable no

/-- The tree *sorts* if, on every input with distinct entries, the permutation it outputs
arranges the input in increasing order. -/
def Sorts (t : CTree) : Prop :=
  ∀ x : Fin 3 → ℕ, Function.Injective x → ∀ a b : Fin 3, a ≤ b → x (run t x a) ≤ x (run t x b)

lemma run_mem_reachable (t : CTree) (x : Fin 3 → ℕ) : run t x ∈ reachable t := by
  induction t with
  | leaf p => simp [run, reachable]
  | cmp i j yes no ihy ihn =>
      by_cases h : x i ≤ x j <;> simp [run, reachable, h, ihy, ihn]

lemma card_reachable_le (t : CTree) : (reachable t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [reachable, depth]
  | cmp i j yes no ihy ihn =>
      refine (Finset.card_union_le _ _).trans ?_
      have h1 : (2 : ℕ) ^ depth yes ≤ 2 ^ (max (depth yes) (depth no)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : (2 : ℕ) ^ depth no ≤ 2 ^ (max (depth yes) (depth no)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : (reachable yes).card + (reachable no).card
          ≤ 2 ^ (max (depth yes) (depth no)) + 2 ^ (max (depth yes) (depth no)) := by
        omega
      simp only [depth, pow_succ]
      omega

/-- A monotone permutation of `Fin 3` is the identity. -/
lemma perm_eq_one_of_monotone (p : Equiv.Perm (Fin 3)) (h : ∀ a b : Fin 3, a ≤ b → p a ≤ p b) :
    p = 1 := by
  revert h; revert p; decide

/-- Every permutation is a possible output of a correct sorting tree. -/
lemma mem_reachable_of_sorts {t : CTree} (ht : Sorts t) (s : Equiv.Perm (Fin 3)) :
    s ∈ reachable t := by
  have hinj : Function.Injective (fun i : Fin 3 => ((s⁻¹ i : Fin 3) : ℕ)) := by
    intro a b hab
    simp only at hab
    have h1 : (s⁻¹ a : Fin 3) = s⁻¹ b := Fin.val_injective hab
    simpa using congrArg (fun z => s z) h1
  have hmono := ht _ hinj
  have key : s⁻¹ * run t (fun i : Fin 3 => ((s⁻¹ i : Fin 3) : ℕ)) = 1 := by
    refine perm_eq_one_of_monotone _ ?_
    intro a b hab
    have h2 := hmono a b hab
    simp only [Equiv.Perm.mul_apply, Fin.le_def]
    simpa using h2
  rw [inv_mul_eq_one.mp key]
  exact run_mem_reachable t _

end CTree

/-- **Comparison-sorting lower bound for 3 elements.**
Any comparison-based sorting algorithm for 3 elements (modelled as a comparison decision
tree that correctly sorts every input with distinct entries) must perform at least
`⌈log₂ 3!⌉ = 3` comparisons in the worst case. -/
theorem sorting_lb_3 (t : CTree) (ht : t.Sorts) : Nat.clog 2 (Nat.factorial 3) ≤ t.depth := by
  have hclog : Nat.clog 2 (Nat.factorial 3) = 3 := by decide
  rw [hclog]
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 3))) ⊆ t.reachable := fun s _ =>
    CTree.mem_reachable_of_sorts ht s
  have hcard : (6 : ℕ) ≤ (t.reachable).card := by
    have h := Finset.card_le_card hsub
    simpa using h
  have hle := CTree.card_reachable_le t
  by_contra hcon
  push_neg at hcon
  have : (2 : ℕ) ^ t.depth ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

namespace CTree

/-- An explicit comparison tree that sorts 3 elements using 3 comparisons. -/
def sortTree3 : CTree :=
  .cmp 0 1
    (.cmp 1 2 (.leaf 1)
      (.cmp 0 2 (.leaf (Equiv.swap 1 2)) (.leaf (Equiv.swap 1 2 * Equiv.swap 0 1))))
    (.cmp 0 2 (.leaf (Equiv.swap 0 1))
      (.cmp 1 2 (.leaf (Equiv.swap 0 1 * Equiv.swap 1 2)) (.leaf (Equiv.swap 0 2))))

lemma sortTree3_depth : sortTree3.depth = 3 := by decide

lemma sortTree3_sorts : sortTree3.Sorts := by
  intro x _ a b hab
  simp only [sortTree3, run]
  by_cases h01 : x 0 ≤ x 1 <;> by_cases h12 : x 1 ≤ x 2 <;> by_cases h02 : x 0 ≤ x 2 <;>
    simp only [h01, h12, h02, if_true, if_false] <;>
    fin_cases a <;> fin_cases b <;>
    simp_all [Equiv.swap_apply_def, Fin.le_def] <;> omega

end CTree

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

