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

theorem dilworth' (α : Type*) [Fintype α] [PartialOrder α] :
    IsGreatest {n : ℕ | ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = n}
        (maxChainCard α) ∧
      IsLeast {n : ℕ | ∃ F : Finset (Finset α), F.card = n ∧
        (∀ A ∈ F, IsAntichain (· ≤ ·) (A : Set α)) ∧ (∀ x : α, ∃ A ∈ F, x ∈ A)}
        (maxChainCard α) :=
  ⟨isGreatest_maxChainCard α, dilworth α _ (isGreatest_maxChainCard α)⟩

end Math

