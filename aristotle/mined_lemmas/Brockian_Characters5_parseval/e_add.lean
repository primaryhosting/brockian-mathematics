import Mathlib

/-!
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
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

namespace Brockian.Characters5

/-- The primitive fifth root of unity `exp (2πi/5)`. -/

lemma e_add (k l : ZMod 5) : e (k + l) = e k * e l := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

