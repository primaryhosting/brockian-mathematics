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
