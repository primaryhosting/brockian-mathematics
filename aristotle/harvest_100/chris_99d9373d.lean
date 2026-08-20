/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree for sorting `4` elements.
A `node (i, j) l r` compares the keys at positions `i` and `j`, descending into `l`
if the key at `i` is smaller and into `r` otherwise.  A `leaf p` outputs the
permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by the tree. -/
def depth : DTree → ℕ
  | leaf _ => 0
  | node _ _ l r => 1 + max (depth l) (depth r)

/-- Running the tree on an input.  The input is a permutation `σ` of `Fin 4`,
interpreted as the assignment of (distinct) keys `σ i` to positions `i`; the
algorithm's only access to the input is through the comparisons `σ i < σ j`. -/
def eval : DTree → Equiv.Perm (Fin 4) → Equiv.Perm (Fin 4)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then eval l σ else eval r σ

/-- A tree *sorts* if, on every input, it outputs the input's key assignment
(equivalently, the permutation needed to sort the input). -/
def Sorts (t : DTree) : Prop := ∀ σ : Equiv.Perm (Fin 4), eval t σ = σ

/-- Key counting lemma: a decision tree of depth `d` can distinguish at most `2 ^ d`
different inputs. -/
theorem card_le_two_pow_depth (t : DTree) :
    ∀ S : Finset (Equiv.Perm (Fin 4)), (∀ σ ∈ S, eval t σ = σ) → S.card ≤ 2 ^ depth t := by
  induction t with
  | leaf p =>
      intro S hS
      have : S ⊆ {p} := by
        intro σ hσ
        have h := hS σ hσ
        rw [eval] at h
        exact Finset.mem_singleton.2 h.symm
      simpa using Finset.card_le_card this
  | node i j l r ihl ihr =>
      intro S hS
      classical
      set A := S.filter (fun σ => σ i < σ j) with hA
      set B := S.filter (fun σ => ¬ (σ i < σ j)) with hB
      have hcard : A.card + B.card = S.card := Finset.card_filter_add_card_filter_not _
      have hAle : A.card ≤ 2 ^ depth l := by
        refine ihl A ?_
        intro σ hσ
        rw [hA, Finset.mem_filter] at hσ
        have := hS σ hσ.1
        rw [eval, if_pos hσ.2] at this
        exact this
      have hBle : B.card ≤ 2 ^ depth r := by
        refine ihr B ?_
        intro σ hσ
        rw [hB, Finset.mem_filter] at hσ
        have := hS σ hσ.1
        rw [eval, if_neg hσ.2] at this
        exact this
      have hl : (2:ℕ) ^ depth l ≤ 2 ^ max (depth l) (depth r) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hr : (2:ℕ) ^ depth r ≤ 2 ^ max (depth l) (depth r) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have : S.card ≤ 2 ^ max (depth l) (depth r) + 2 ^ max (depth l) (depth r) := by
        omega
      simpa [depth, pow_succ, pow_add, two_mul, Nat.add_comm] using this

end DTree

/-- **Sorting lower bound for 4 elements.**
Any comparison sort of `4` elements needs at least `⌈log₂ (4!)⌉ = 5` comparisons in the
worst case: any comparison decision tree that correctly sorts every input of length `4`
has depth at least `Nat.clog 2 (4!) = 5`. -/
theorem sorting_lb_4 (t : DTree) (ht : t.Sorts) :
    Nat.clog 2 (Nat.factorial 4) ≤ t.depth := by
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by
    simp [Finset.card_univ, Fintype.card_perm]
    decide
  have h := DTree.card_le_two_pow_depth t Finset.univ (fun σ _ => ht σ)
  rw [hcard] at h
  have hclog : Nat.clog 2 (Nat.factorial 4) = 5 := by decide
  rw [hclog]
  by_contra hlt
  push_neg at hlt
  have : (2:ℕ) ^ t.depth ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CS

#print axioms CS.sorting_lb_4

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

