import Mathlib
/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

namespace QC

/-- The sign `(-1)^b` of a bit, as a complex number. -/

theorem probOne_of_const (f : Bool → Bool) (h : f false = f true) : probOne f = 0 := by
  simp only [probOne, deutsch_amp_one, h]
  cases ht : f true <;> simp [sgn]

/-- If `f` is balanced, the algorithm measures `1` on the first qubit with certainty. -/
