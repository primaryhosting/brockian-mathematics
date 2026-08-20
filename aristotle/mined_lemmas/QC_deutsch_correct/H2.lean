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

noncomputable def H2 (psi : Bool × Bool → ℂ) : Bool × Bool → ℂ :=
  fun p => (psi (p.1, false) + sgn p.2 * psi (p.1, true)) / rt2

/-- The oracle `U_f : |x, y⟩ ↦ |x, y ⊕ f x⟩` for `f : Bool → Bool`. -/
