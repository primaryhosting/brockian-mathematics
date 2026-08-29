/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset Filter Asymptotics

/-- The number of points of `𝔽₃ⁿ`, where `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`. -/

lemma card_F3pow (n : ℕ) : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by
  simp

/-- For every `ε > 0` there is an `N` beyond which the constant coming from the corners
