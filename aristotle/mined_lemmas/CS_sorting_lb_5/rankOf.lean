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

def rankOf (f : Fin 5 → Fin 5 → Bool) (i : Fin 5) : Fin 5 :=
  ⟨(Finset.univ.filter (fun j => j ≠ i ∧ f j i = true)).card, by
    have hsub : (Finset.univ.filter (fun j => j ≠ i ∧ f j i = true)) ⊆
        (Finset.univ.erase i) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_erase.mpr ⟨hj.1, Finset.mem_univ j⟩
    have := Finset.card_le_card hsub
    have h4 : (Finset.univ.erase i).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp
    omega⟩

/-- The permutation output at a leaf: the inverse of the rank function, when the
recorded answers make the rank function a bijection. -/
