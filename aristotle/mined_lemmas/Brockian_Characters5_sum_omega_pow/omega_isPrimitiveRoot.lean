/-
# Sum Omega Pow
Category: Characters
Target: Brockian.Characters5.sum_omega_pow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sum Omega Pow
Category: Characters
Target: Brockian.Characters5.sum_omega_pow
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

namespace Brockian.Characters5

/-- A primitive 5th root of unity. -/

theorem omega_isPrimitiveRoot : IsPrimitiveRoot ω 5 := by
  simpa [omega, mul_comm, mul_assoc, mul_left_comm] using
    Complex.isPrimitiveRoot_exp 5 (by norm_num)

/-- The sum of all five 5th roots of unity vanishes. -/
