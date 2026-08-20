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

lemma exists_chain_chainHeight (x : α) :
    ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ (∀ y ∈ s, y ≤ x) ∧ s.card = chainHeight x := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset α))
    ⟨(∅ : Finset α), Finset.mem_univ _⟩
    (fun s : Finset α =>
      if IsChain (· ≤ ·) (s : Set α) ∧ ∀ y ∈ s, y ≤ x then s.card else 0)
  by_cases hcond : IsChain (· ≤ ·) (s : Set α) ∧ ∀ y ∈ s, y ≤ x
  · refine ⟨s, hcond.1, hcond.2, ?_⟩
    rw [chainHeight, hs, if_pos hcond]
  · exfalso
    have : chainHeight x = 0 := by rw [chainHeight, hs, if_neg hcond]
    have := one_le_chainHeight x
    omega

