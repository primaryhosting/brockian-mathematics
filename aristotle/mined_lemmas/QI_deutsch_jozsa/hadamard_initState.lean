import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

namespace QI

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

lemma hadamard_initState : hadamard (initState n) = fun _ => hcoeff n := by
  funext y
  simp [hadamard, initState, chi_zeroStr_left]

/-- The amplitude of the all-zeros outcome is the normalized `±1` average of `f`. -/
