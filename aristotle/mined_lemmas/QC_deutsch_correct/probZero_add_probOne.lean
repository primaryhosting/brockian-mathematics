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

theorem probZero_add_probOne (f : Bool → Bool) : probZero f + probOne f = 1 := by
  by_cases h : f false = f true
  · rw [probZero_of_const f h, probOne_of_const f h]; norm_num
  · rw [probZero_of_balanced f h, probOne_of_balanced f h]; norm_num

/-- **Deutsch's algorithm is correct.** Using a single query to the oracle `U_f`, the
measurement of the first qubit of the final state distinguishes constant from balanced
functions with certainty: the outcome is `0` with probability `1` exactly when `f` is
constant, and it is `1` with probability `1` (equivalently, `0` occurs with probability
`0`) exactly when `f` is balanced. -/
