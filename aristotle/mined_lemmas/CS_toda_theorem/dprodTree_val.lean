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

/-
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


theorem dprodTree_val (n : ℕ) (x : Assign) (D : ℕ → GapData) (hD : ∀ i, Disj (D i)) :
    ∀ (d off : ℕ),
      (dprodTree n D d off).val n x = ∏ j ∈ Finset.range (2 ^ d), (D (off + j)).val n x
  | 0, off => by simp [dprodTree]
  | (d + 1), off => by
      rw [dprodTree, dmul_val n x _ _ (dprodTree_disj n D hD d off)
        (dprodTree_disj n D hD d (off + 2 ^ d)),
        dprodTree_val n x D hD d off, dprodTree_val n x D hD d (off + 2 ^ d)]
      have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      rw [h2, Finset.prod_range_add]
      congr 1
      exact Finset.prod_congr rfl fun j _ => by rw [add_assoc]

