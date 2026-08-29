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

noncomputable def probOne (f : Bool → Bool) : ℝ :=
  ‖deutsch f (true, false)‖ ^ 2 + ‖deutsch f (true, true)‖ ^ 2

/-- Closed form for the amplitudes of the final state on the basis vectors whose first
qubit is `0`: they are proportional to `(-1)^{f 0} + (-1)^{f 1}`. -/
