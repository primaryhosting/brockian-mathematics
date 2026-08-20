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

theorem e_mul_val (a k : ZMod 5) : e (a * k) = e k ^ a.val := by
  rw [← e_nsmul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]

