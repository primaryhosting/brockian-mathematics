/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
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

set_option grind.warning false

namespace Math

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- A colouring of the poset by `{0, …, n-1}` whose colour classes are antichains. -/

lemma coverable_longestChain :
    ∃ f : α → ℕ, IsAntichainColoring (longestChain α) f := by
  refine ⟨fun x => height' x - 1, ?_, ?_⟩
  · intro x
    show height' x - 1 < longestChain α
    have h1 := one_le_height' x
    have h2 := height'_le x
    omega
  · intro x y hxy hle
    have hxy' : height' x - 1 = height' y - 1 := hxy
    by_contra hne
    have hlt : x < y := lt_of_le_of_ne hle hne
    have h3 := height'_strictMono hlt
    have h1 := one_le_height' x
    have h2 := one_le_height' y
    omega

