/-
# Sorting Lb 3
Category: Computer Science
Target: CS.sorting_lb_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

/-- A comparison-based decision tree for sorting `3` elements.

An internal node `cmp i j l r` performs the comparison "is the element at position `i`
smaller than the element at position `j`?" and branches accordingly; a leaf reports the
permutation that the algorithm claims describes the input order. -/
inductive DTree3 : Type
  | leaf (out : Equiv.Perm (Fin 3)) : DTree3
  | cmp (i j : Fin 3) (l r : DTree3) : DTree3
  deriving Inhabited

namespace DTree3

/-- The worst-case number of comparisons performed by the decision tree, i.e. its depth. -/
def depth : DTree3 → ℕ
  | leaf _ => 0
  | cmp _ _ l r => max (depth l) (depth r) + 1

/-- Running the decision tree on the input whose element ranks are given by `σ`:
the element at position `i` has rank `σ i`, so the comparison at node `cmp i j`
answers `σ i < σ j`. -/
def run : DTree3 → Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)
  | leaf o, _ => o
  | cmp i j l r, σ => if σ i < σ j then run l σ else run r σ

/-- The finite set of outputs appearing at the leaves of the tree. -/
def outputs : DTree3 → Finset (Equiv.Perm (Fin 3))
  | leaf o => {o}
  | cmp _ _ l r => outputs l ∪ outputs r

/-- A tree *sorts* if on every input it correctly reports the input's order. -/
def Sorts (t : DTree3) : Prop := ∀ σ : Equiv.Perm (Fin 3), run t σ = σ

lemma run_mem_outputs (t : DTree3) (σ : Equiv.Perm (Fin 3)) : run t σ ∈ outputs t := by
  induction t with
  | leaf o => simp [run, outputs]
  | cmp i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, outputs, h, ihl, ihr]

/-- A binary decision tree of depth `d` has at most `2 ^ d` distinct leaf outputs. -/
lemma card_outputs_le (t : DTree3) : (outputs t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf o => simp [outputs, depth]
  | cmp i j l r ihl ihr =>
      have h1 : (outputs l ∪ outputs r).card ≤ (outputs l).card + (outputs r).card :=
        Finset.card_union_le _ _
      have h2 : (outputs l).card ≤ 2 ^ max (depth l) (depth r) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h3 : (outputs r).card ≤ 2 ^ max (depth l) (depth r) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have : (outputs (cmp i j l r)).card ≤ 2 ^ max (depth l) (depth r)
          + 2 ^ max (depth l) (depth r) := by
        simpa [outputs] using h1.trans (Nat.add_le_add h2 h3)
      simpa [depth, pow_succ, Nat.mul_two] using this

/-- A sorting decision tree must have all `3! = 6` permutations among its leaf outputs. -/
lemma card_outputs_ge_of_sorts {t : DTree3} (h : Sorts t) : 6 ≤ (outputs t).card := by
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 3))) ⊆ outputs t := by
    intro σ _
    have := run_mem_outputs t σ
    rwa [h σ] at this
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by
    simp [Finset.card_univ, Fintype.card_perm, Nat.factorial]
  calc (6 : ℕ) = (Finset.univ : Finset (Equiv.Perm (Fin 3))).card := hcard.symm
    _ ≤ (outputs t).card := Finset.card_le_card hsub

end DTree3

/-- **Comparison-sorting lower bound for 3 elements.**
Any comparison-based decision tree that correctly sorts `3` elements must, in the worst
case, perform at least `⌈log₂ (3!)⌉ = 3` comparisons. -/
theorem sorting_lb_3 (t : DTree3) (h : DTree3.Sorts t) :
    Nat.clog 2 (Nat.factorial 3) ≤ DTree3.depth t := by
  have hclog : Nat.clog 2 (Nat.factorial 3) = 3 := by decide
  rw [hclog]
  by_contra hlt
  push_neg at hlt
  have hd : DTree3.depth t ≤ 2 := by omega
  have h1 : (DTree3.outputs t).card ≤ 2 ^ DTree3.depth t := DTree3.card_outputs_le t
  have h2 : (2 : ℕ) ^ DTree3.depth t ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hd
  have h3 : 6 ≤ (DTree3.outputs t).card := DTree3.card_outputs_ge_of_sorts h
  omega


/-- The bound is tight and non-vacuous: there is a comparison-based decision tree of
depth exactly `3` that correctly sorts `3` elements. -/
theorem exists_sorting_tree_depth_three :
    ∃ t : DTree3, DTree3.Sorts t ∧ DTree3.depth t = 3 := by
  refine ⟨DTree3.cmp 0 1
      (DTree3.cmp 1 2
        (DTree3.leaf 1)
        (DTree3.cmp 0 2
          (DTree3.leaf (Equiv.swap 1 2))
          (DTree3.leaf (Equiv.swap 0 1 * Equiv.swap 1 2))))
      (DTree3.cmp 0 2
        (DTree3.leaf (Equiv.swap 0 1))
        (DTree3.cmp 1 2
          (DTree3.leaf (Equiv.swap 1 2 * Equiv.swap 0 1))
          (DTree3.leaf (Equiv.swap 0 2)))), ?_, ?_⟩
  · unfold DTree3.Sorts
    decide
  · decide

end CS

