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

lemma card_le_maxChainCard {C : Finset α} (hC : IsChain (· ≤ ·) (↑C : Set α)) :
    C.card ≤ maxChainCard α :=
  Finset.le_sup (f := Finset.card) (mem_chainsOf.2 hC)

