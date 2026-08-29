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

def valAux {n : ℕ} (c : ℕ → Gate n) (x : Cube n) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, g =>
    match c g with
    | .var i => x i
    | .neg j => if j < g then !(valAux c x fuel j) else false
    | .conj s => decide (∀ j ∈ s, j < g → valAux c x fuel j = true)
    | .disj s => decide (∃ j ∈ s, j < g ∧ valAux c x fuel j = true)

/-- Value of gate `g` of the circuit `c` on input `x`. -/
