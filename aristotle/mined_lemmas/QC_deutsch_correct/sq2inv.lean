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

/-! ## Setup

We model a two–qubit system by its amplitude function on the computational basis
`Bool × Bool`, the first component being the query register and the second the
answer register.  All gates are the usual `2 × 2` (resp. `4 × 4`) unitaries written
out on amplitudes. -/

/-- The scalar `1/√2` occurring in the Hadamard gate. -/

noncomputable def sq2inv : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- `sgn b = (-1)^b`. -/
