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

/-! ## The two-qubit state space

A state of two qubits is a function `Bool × Bool → ℂ` assigning an amplitude to each
computational basis state `|x y⟩`. -/

/-- The sign `(-1)^b`. -/

noncomputable def prob1 (f : Bool → Bool) : ℝ :=
  ‖deutschState f (true, false)‖ ^ 2 + ‖deutschState f (true, true)‖ ^ 2

/-- Explicit form of the amplitudes of the final state on the first qubit being `1`. -/
