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

lemma one_le_chainHeight (x : α) : 1 ≤ chainHeight x := by
  classical
  have h := Finset.le_sup (f := fun s : Finset α =>
      if IsChain (· ≤ ·) (s : Set α) ∧ ∀ y ∈ s, y ≤ x then s.card else 0)
    (Finset.mem_univ ({x} : Finset α))
  have hcond : IsChain (· ≤ ·) (({x} : Finset α) : Set α) ∧ ∀ y ∈ ({x} : Finset α), y ≤ x := by
    refine ⟨?_, ?_⟩
    · simp [Finset.coe_singleton, Set.Subsingleton.isChain]
    · intro y hy
      simp only [Finset.mem_singleton] at hy
      exact hy.le
  rw [chainHeight]
  simpa [hcond] using h

