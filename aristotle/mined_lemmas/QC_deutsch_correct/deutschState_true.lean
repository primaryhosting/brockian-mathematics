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

lemma deutschState_true (f : Bool → Bool) (y : Bool) :
    deutschState f (true, y) = sgn y * (sgn (f false) - sgn (f true)) / (2 * rt2) := by
  simp only [deutschState, H1, H2, oracle, init, sgn]
  cases y <;> cases f false <;> cases f true <;> simp <;>
    field_simp [rt2_ne_zero] <;> (simp only [rt2_sq]; try ring)

/-- The complementary outcome: the first qubit is measured to be `1` exactly when `f` is
balanced. -/
