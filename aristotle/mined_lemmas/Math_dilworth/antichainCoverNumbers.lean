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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Finset

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains (as finsets) of a finite partial order. -/

def antichainCoverNumbers (α : Type*) [PartialOrder α] : Set ℕ :=
  {n | ∃ A : Fin n → Set α, (∀ i, IsAntichain (· ≤ ·) (A i)) ∧ ∀ x : α, ∃ i, x ∈ A i}

/-- The minimal number of antichains needed to cover a finite partial order. -/
