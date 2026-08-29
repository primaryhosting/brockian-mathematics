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

noncomputable def had₁ (ψ : State) : State :=
  fun p => ((Real.sqrt 2)⁻¹ : ℝ) * (ψ (false, p.2) + sgn p.1 * ψ (true, p.2))

/-- The Hadamard gate applied to the second qubit. -/
