import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

open Finset Asymptotics Filter

/-- The cap set number `capSetNumber n` is the largest cardinality of a subset of
`𝔽₃ⁿ = (Fin n → ZMod 3)` containing no nontrivial three-term arithmetic progression. -/

lemma card_F3 (n : ℕ) : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by
  simp

/-- Quantitative form of the cap set theorem: for every `ε > 0` there is `N` such that for all
`n ≥ N`, every 3AP-free subset of `𝔽₃ⁿ` has fewer than `ε * 3ⁿ` elements. -/
