/-
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
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

namespace Brockian

namespace Characters5

/-- A primitive fifth root of unity. -/

theorem e_ne_one (k : ZMod 5) (hk : k ≠ 0) : e k ≠ 1 :=
  isPrimitiveRoot_omega.pow_ne_one_of_pos_of_lt
    (fun h => hk ((ZMod.val_eq_zero k).mp h)) (ZMod.val_lt k)

/-- Orthogonality of the characters on `ZMod 5`. -/
