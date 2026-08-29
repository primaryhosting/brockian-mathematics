/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
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

/-- A comparison-based decision tree sorting 5 elements: an internal node
`node i j l r` compares the keys at positions `i` and `j`, descending into `l`
when `a i ≤ a j` and into `r` otherwise; a leaf outputs a permutation of the
positions. -/
inductive CompTree where
  | leaf : Equiv.Perm (Fin 5) → CompTree
  | node : Fin 5 → Fin 5 → CompTree → CompTree → CompTree
  deriving Inhabited

namespace CompTree

/-- The worst-case number of comparisons performed by the decision tree. -/

lemma rankOf_strictMono (a : Fin 5 → ℕ) {i j : Fin 5}
    (hlt : a i < a j) :
    rankOf (fun x y => decide (a x ≤ a y)) i < rankOf (fun x y => decide (a x ≤ a y)) j := by
  rw [Fin.lt_def, rankOf_val, rankOf_val]
  apply Finset.card_lt_card
  constructor
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    refine ⟨?_, le_of_lt (lt_of_le_of_lt hk.2 hlt)⟩
    intro hkj
    exact absurd (hkj ▸ hk.2) (not_le.mpr hlt)
  · intro hsub
    have hi : i ∈ Finset.univ.filter (fun k => k ≠ j ∧ a k ≤ a j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => absurd (h ▸ hlt) (lt_irrefl _), le_of_lt hlt⟩
    have := hsub hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.1 rfl

