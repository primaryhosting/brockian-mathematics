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

section Mirsky

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- The finset of all chains of a finite partial order. -/

noncomputable def chainsOf (α : Type*) [Fintype α] [PartialOrder α] : Finset (Finset α) :=
  Finset.univ.filter (fun C : Finset α => IsChain (· ≤ ·) (↑C : Set α))

