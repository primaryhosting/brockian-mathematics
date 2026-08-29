/-
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The Hadamard matrix entry `H a b = (-1)^(a ∧ b) / √2`. -/

noncomputable def had (a b : Bool) : ℂ := (if a && b then -1 else 1) / (Real.sqrt 2 : ℝ)

/-- The initial two–qubit state `|0⟩|1⟩`, as an amplitude function on `Bool × Bool`. -/
