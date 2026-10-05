import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A comparison-based decision tree for sorting four elements.
Each internal node compares two positions `i j` of the input; the algorithm
branches on the answer.  Each leaf outputs a permutation (the claimed sorted
order of the input). -/
inductive CompTree : Type
  | leaf (out : Equiv.Perm (Fin 4)) : CompTree
  | node (i j : Fin 4) (l r : CompTree) : CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the tree. -/
def depth : CompTree → ℕ
  | leaf _ => 0
  | node _ _ l r => max (depth l) (depth r) + 1

/-- Running the algorithm on the input whose ranking function is `p`:
element `i` has rank `p i`, and a comparison of `i` and `j` answers whether
`p i < p j`. -/
def run : CompTree → Equiv.Perm (Fin 4) → Equiv.Perm (Fin 4)
  | leaf o, _ => o
  | node i j l r, p => if p i < p j then run l p else run r p

/-- The (finite) set of outputs the tree can produce. -/
def leaves : CompTree → Finset (Equiv.Perm (Fin 4))
  | leaf o => {o}
  | node _ _ l r => leaves l ∪ leaves r

theorem run_mem_leaves (t : CompTree) (p : Equiv.Perm (Fin 4)) :
    t.run p ∈ t.leaves := by
  induction t with
  | leaf o => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : p i < p j <;> simp [run, leaves, h, ihl, ihr]

/-- A decision tree of depth `d` has at most `2 ^ d` distinct outputs. -/
theorem card_leaves_le (t : CompTree) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf o => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc l.leaves.card + r.leaves.card
          ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := add_le_add hl hr
        _ = 2 ^ (depth (node i j l r)) := by simp [depth, pow_succ]; ring

/-- A tree *sorts correctly* if, on every input ranking `p`, it outputs `p`
(equivalently, it determines the correct ordering of the four elements). -/
def Sorts (t : CompTree) : Prop := ∀ p : Equiv.Perm (Fin 4), t.run p = p

/-- The six comparisons between distinct positions of a four-element input. -/
def allPairs : List (Fin 4 × Fin 4) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The naive algorithm: perform the comparisons in the given list one after the
other, keeping track of the set `S` of still-possible orderings, and finally
output an element of `S`. -/
noncomputable def build : Finset (Equiv.Perm (Fin 4)) → List (Fin 4 × Fin 4) → CompTree
  | S, [] => leaf S.toList.headI
  | S, (i, j) :: rest =>
      node i j (build (S.filter fun q => q i < q j) rest)
        (build (S.filter fun q => ¬ q i < q j) rest)

theorem run_build (l : List (Fin 4 × Fin 4)) :
    ∀ (S : Finset (Equiv.Perm (Fin 4))) (p : Equiv.Perm (Fin 4)), p ∈ S →
      run (build S l) p =
        (S.filter fun q => ∀ ij ∈ l, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2)).toList.headI := by
  induction l with
  | nil =>
      intro S p _
      simp [build, run]
  | cons ij rest ih =>
      obtain ⟨i, j⟩ := ij
      intro S p hp
      by_cases h : p i < p j
      · have hmem : p ∈ S.filter fun q => q i < q j := Finset.mem_filter.mpr ⟨hp, h⟩
        have hrun : run (build S ((i, j) :: rest)) p
            = run (build (S.filter fun q => q i < q j) rest) p := by simp [build, run, h]
        have hset : ((S.filter fun q => q i < q j).filter
              fun q => ∀ ij ∈ rest, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2))
            = S.filter fun q => ∀ ij ∈ (i, j) :: rest, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2) := by
          ext q
          simp only [Finset.mem_filter, List.mem_cons, forall_eq_or_imp]
          tauto
        rw [hrun, ih _ p hmem, hset]
      · have hmem : p ∈ S.filter fun q => ¬ q i < q j := Finset.mem_filter.mpr ⟨hp, h⟩
        have hrun : run (build S ((i, j) :: rest)) p
            = run (build (S.filter fun q => ¬ q i < q j) rest) p := by simp [build, run, h]
        have hset : ((S.filter fun q => ¬ q i < q j).filter
              fun q => ∀ ij ∈ rest, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2))
            = S.filter fun q => ∀ ij ∈ (i, j) :: rest, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2) := by
          ext q
          simp only [Finset.mem_filter, List.mem_cons, forall_eq_or_imp]
          tauto
        rw [hrun, ih _ p hmem, hset]

theorem eq_of_allPairs (p q : Equiv.Perm (Fin 4))
    (h : ∀ ij ∈ allPairs, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2)) : q = p := by
  revert h
  revert p q
  decide

/-- The hypothesis of the lower bound is satisfiable: some decision tree really
does sort four elements (the naive one, using all six comparisons). -/
theorem exists_sorts : ∃ t : CompTree, t.Sorts := by
  refine ⟨build Finset.univ allPairs, fun p => ?_⟩
  rw [run_build allPairs Finset.univ p (Finset.mem_univ p)]
  have : (Finset.univ.filter fun q : Equiv.Perm (Fin 4) =>
      ∀ ij ∈ allPairs, (q ij.1 < q ij.2 ↔ p ij.1 < p ij.2)) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨eq_of_allPairs p q, fun hq => by simp [hq]⟩
  rw [this]
  simp

end CompTree

/-- **Comparison-sort lower bound for 4 elements.**
Any comparison-based sorting algorithm on four elements, modelled as a decision
tree that correctly recovers the input ordering, performs at least
`⌈log₂ (4!)⌉ = 5` comparisons in the worst case. -/
theorem sorting_lb_4 (t : CompTree) (ht : t.Sorts) :
    Nat.clog 2 (Nat.factorial 4) ≤ t.depth := by
  have hcl : Nat.clog 2 (Nat.factorial 4) = 5 := by decide
  rw [hcl]
  -- every permutation is an output of `t`
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 4))) ⊆ t.leaves := by
    intro p _
    have := t.run_mem_leaves p
    rwa [ht p] at this
  have hcard : (24 : ℕ) ≤ t.leaves.card := by
    have h1 : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card ≤ t.leaves.card :=
      Finset.card_le_card hsub
    simpa using h1
  by_contra h
  push_neg at h
  have hle : (2 : ℕ) ^ t.depth ≤ 2 ^ 4 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have := t.card_leaves_le
  norm_num at hle
  omega

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

