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
