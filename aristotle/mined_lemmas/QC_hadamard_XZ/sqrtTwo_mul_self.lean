/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment because Lean 4 requires
-- `import` commands to precede any module docstring.)

import Mathlib

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

/-- The Pauli `X` gate. -/

lemma sqrtTwo_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

/-- **Hadamard from Paulis, and conjugation of `X`.**
The Hadamard gate equals `(X + Z)/√2`, and it conjugates `X` into `Z`. -/
