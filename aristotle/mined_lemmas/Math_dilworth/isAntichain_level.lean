/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

open Classical in
/-- `chainHeight x` is the largest cardinality of a chain all of whose elements are `≤ x`. -/

lemma isAntichain_level (k : ℕ) :
    IsAntichain (· ≤ ·)
      ((Finset.univ.filter (fun x : α => chainHeight x - 1 = k) : Finset α) : Set α) := by
  classical
  intro a ha b hb hab hle
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
  have hlt : a < b := lt_of_le_of_ne hle hab
  have := chainHeight_lt_of_lt hlt
  have h1 := one_le_chainHeight a
  have h2 := one_le_chainHeight b
  omega

omit [Fintype α] in
/-- A cover by antichains has at least as many parts as any chain has elements. -/
