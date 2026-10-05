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

theorem probZero_of_const (f : Bool → Bool) (h : f false = f true) : probZero f = 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    have h63 : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
    rw [h63, hs]; norm_num
  simp only [probZero, deutsch_amp, h]
  cases ht : f true <;>
    simp [sgn, Complex.norm_real, mul_pow, abs_of_nonneg, Real.sqrt_nonneg] <;>
    field_simp <;> norm_num [h6]

/-- If `f` is balanced, the algorithm never measures `0` on the first qubit. -/
