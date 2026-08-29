/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- A comparison-based sorting algorithm on 4 elements, modelled as a (binary) decision tree.
A `node i j l r` performs the comparison "is the element in position `i` smaller than or equal
to the element in position `j`?" and continues in the subtree `l` (resp. `r`) if the answer is
yes (resp. no).  A `leaf q` reports that the input arrangement is `q`.
The model is fully adaptive: the comparison performed at each step may depend on all previous
answers. -/
inductive CompTree : Type
  | leaf : Equiv.Perm (Fin 4) → CompTree
  | node : Fin 4 → Fin 4 → CompTree → CompTree → CompTree

namespace CompTree

/-- The worst-case number of comparisons performed by the algorithm, i.e. the depth of the tree. -/
def depth : CompTree → ℕ
  | leaf _ => 0
  | node _ _ l r => 1 + max l.depth r.depth

/-- Running the algorithm on the input whose ranking is described by the permutation `p`
(the element in position `i` has rank `p i`).  The comparisons are answered consistently
with `p`, and the result is the arrangement reported by the leaf that is reached. -/
def run : CompTree → Equiv.Perm (Fin 4) → Equiv.Perm (Fin 4)
  | leaf q, _ => q
  | node i j l r, p => if p i ≤ p j then l.run p else r.run p

/-- An algorithm *sorts* if, on every one of the `4!` possible input arrangements, it correctly
identifies that arrangement (equivalently: it outputs the permutation needed to sort the input). -/
def Sorts (t : CompTree) : Prop := ∀ p : Equiv.Perm (Fin 4), t.run p = p

/-- Key counting lemma: the number of input arrangements that a decision tree of depth `d`
can correctly identify is at most `2 ^ d` (a tree of depth `d` has at most `2 ^ d` leaves). -/
theorem card_correct_le (t : CompTree) :
    (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => t.run p = p).card ≤ 2 ^ t.depth := by
  induction t with
  | leaf q =>
      rw [depth, pow_zero]
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, run] at ha hb
      rw [← ha, ← hb]
  | node i j l r ihl ihr =>
      have hsub :
          (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => (node i j l r).run p = p) ⊆
            (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => l.run p = p) ∪
              (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => r.run p = p) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, run] at hp
        by_cases h : p i ≤ p j
        · rw [if_pos h] at hp
          simp [Finset.mem_union, hp]
        · rw [if_neg h] at hp
          simp [Finset.mem_union, hp]
      have hmax : ∀ s : CompTree, s.depth ≤ max l.depth r.depth → (2 : ℕ) ^ s.depth ≤ 2 ^ (max l.depth r.depth) :=
        fun s hs => Nat.pow_le_pow_right (by norm_num) hs
      calc (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => (node i j l r).run p = p).card
          ≤ ((Finset.univ.filter fun p : Equiv.Perm (Fin 4) => l.run p = p) ∪
              (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => r.run p = p)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => l.run p = p).card +
              (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => r.run p = p).card :=
            Finset.card_union_le _ _
        _ ≤ 2 ^ l.depth + 2 ^ r.depth := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) :=
            Nat.add_le_add (hmax l (le_max_left _ _)) (hmax r (le_max_right _ _))
        _ = 2 ^ (1 + max l.depth r.depth) := by ring
        _ = 2 ^ (node i j l r).depth := by rw [depth]

/-- Two arrangements that give the same answer to every comparison are equal. -/
theorem perm_eq_of_comparisons_eq (p q : Equiv.Perm (Fin 4))
    (h : ∀ i j : Fin 4, p i ≤ p j ↔ q i ≤ q j) : p = q := by
  have hmono : Monotone ⇑(p.symm.trans q) := by
    intro a b hab
    have := (h (p.symm a) (p.symm b)).1 (by simpa using hab)
    simpa using this
  have h1 : p.symm.trans q = 1 := (Equiv.Perm.monotone_iff _).1 hmono
  refine Equiv.ext fun i => ?_
  have := Equiv.ext_iff.1 h1 (p i)
  simpa using this.symm

/-- For every set of arrangements there is a decision tree identifying each of them: repeatedly
split the remaining candidates by a comparison on which two of them disagree. -/
theorem exists_tree_correct_on (s : Finset (Equiv.Perm (Fin 4))) :
    ∃ t : CompTree, ∀ p ∈ s, t.run p = p := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    by_cases hcard : s.card ≤ 1
    · have h := Finset.card_le_one.1 hcard
      by_cases he : s = ∅
      · exact ⟨CompTree.leaf 1, by simp [he]⟩
      · obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.2 he
        exact ⟨CompTree.leaf q, fun p hp => h q hq p hp⟩
    · push_neg at hcard
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hcard
      have hnot : ¬ (∀ i j : Fin 4, p i ≤ p j ↔ q i ≤ q j) :=
        fun hh => hpq (perm_eq_of_comparisons_eq p q hh)
      push_neg at hnot
      obtain ⟨i, j, hij⟩ := hnot
      have hne : ¬ ((p i ≤ p j) ↔ (q i ≤ q j)) := by
        rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact fun hiff => absurd (hiff.1 h1) (not_le.2 h2)
        · exact fun hiff => absurd (hiff.2 h2) (not_le.2 h1)
      have hsub1 : s.filter (fun r : Equiv.Perm (Fin 4) => r i ≤ r j) ⊂ s := by
        refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ?_
        by_cases hpij : p i ≤ p j
        · have hqij : ¬ (q i ≤ q j) := fun hh => hne ⟨fun _ => hh, fun _ => hpij⟩
          exact ⟨q, hq, fun hmem => hqij (Finset.mem_filter.1 hmem).2⟩
        · exact ⟨p, hp, fun hmem => hpij (Finset.mem_filter.1 hmem).2⟩
      have hsub2 : s.filter (fun r : Equiv.Perm (Fin 4) => ¬ (r i ≤ r j)) ⊂ s := by
        refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ?_
        by_cases hpij : p i ≤ p j
        · exact ⟨p, hp, fun hmem => (Finset.mem_filter.1 hmem).2 hpij⟩
        · have hqij : q i ≤ q j := by
            by_contra hh
            exact hne ⟨fun hx => absurd hx hpij, fun hx => absurd hx hh⟩
          exact ⟨q, hq, fun hmem => (Finset.mem_filter.1 hmem).2 hqij⟩
      obtain ⟨t₁, ht₁⟩ := ih _ hsub1
      obtain ⟨t₂, ht₂⟩ := ih _ hsub2
      refine ⟨CompTree.node i j t₁ t₂, fun r hr => ?_⟩
      by_cases hrij : r i ≤ r j
      · simp only [CompTree.run, if_pos hrij]
        exact ht₁ r (Finset.mem_filter.2 ⟨hr, hrij⟩)
      · simp only [CompTree.run, if_neg hrij]
        exact ht₂ r (Finset.mem_filter.2 ⟨hr, hrij⟩)

end CompTree

/-- Sorting comparison trees do exist, so the lower bound below is not vacuous. -/
theorem exists_sorting_tree : ∃ t : CompTree, t.Sorts := by
  obtain ⟨t, ht⟩ := CompTree.exists_tree_correct_on Finset.univ
  exact ⟨t, fun p => ht p (Finset.mem_univ p)⟩

/-- `⌈log₂ (4!)⌉ = 5`. -/
theorem clog_two_factorial_four : Nat.clog 2 (Nat.factorial 4) = 5 := by
  norm_num [Nat.factorial]

/-- **Comparison-sorting lower bound for 4 elements.**
Any comparison sort of `4` elements needs at least `⌈log₂ (4!)⌉ = 5` comparisons in the worst
case: if a comparison decision tree correctly identifies every one of the `4!` input
arrangements, then its depth is at least `Nat.clog 2 (4!) = 5`. -/
theorem sorting_lb_4 (t : CompTree) (ht : t.Sorts) :
    Nat.clog 2 (Nat.factorial 4) ≤ t.depth := by
  -- All `24` arrangements are correctly identified, so `24 ≤ 2 ^ depth`.
  have hall : (Finset.univ.filter fun p : Equiv.Perm (Fin 4) => t.run p = p)
      = (Finset.univ : Finset (Equiv.Perm (Fin 4))) := by
    apply Finset.filter_true_of_mem
    intro p _
    exact ht p
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = Nat.factorial 4 := by
    simp [Finset.card_univ, Fintype.card_perm]
  have h24 : Nat.factorial 4 ≤ 2 ^ t.depth := by
    have := t.card_correct_le
    rwa [hall, hcard] at this
  -- Hence `depth ≥ ⌈log₂ 24⌉ = 5`.
  exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 h24

end CS

