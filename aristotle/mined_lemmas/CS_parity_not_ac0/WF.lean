/-
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
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

namespace CS

/-! ## The Boolean cube and `ZMod 3`-valued functions on it -/

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Functions from the Boolean cube to the field `ZMod 3`. -/
abbrev CFun (n : ℕ) := Cube n → ZMod 3

/-- The `±1` encoding of a bit inside `ZMod 3`. -/

def WF {n : ℕ} (c : ℕ → Gate n) (out : ℕ) : Prop :=
  ∀ g ≤ out, ∀ j ∈ (c g).inputs, j < g

/-- Fuel-based evaluation of the gates of a circuit. References to gates that are not strictly
earlier are ignored (they cannot occur in a well-formed circuit). -/
