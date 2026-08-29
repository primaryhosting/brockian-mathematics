import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
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

namespace Math2

open Finset

variable {n : ℕ}

/-- The shadow of a family `𝒜` of finite sets: all the sets obtained from a member of `𝒜` by
deleting one element. -/

def ColexLt (s t : Finset (Fin n)) : Prop := ∃ a ∈ t, a ∉ s ∧ ∀ b ∈ s, b ∉ t → b < a

