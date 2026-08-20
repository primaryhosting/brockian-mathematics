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

lemma chainHeight_le_of_isGreatest {M : ℕ}
    (hM : IsGreatest {n : ℕ | ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = n} M)
    (x : α) : chainHeight x ≤ M := by
  classical
  rw [chainHeight]
  refine Finset.sup_le ?_
  intro s _
  split
  · rename_i hs
    exact hM.2 ⟨s, hs.1, rfl⟩
  · exact Nat.zero_le _

