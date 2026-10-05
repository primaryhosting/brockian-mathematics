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

theorem probOne_of_balanced (f : Bool → Bool) (h : f false ≠ f true) : probOne f = 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    have h63 : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
    rw [h63, hs]; norm_num
  simp only [probOne, deutsch_amp_one]
  cases hf : f false <;> cases ht : f true <;> rw [hf, ht] at h <;>
    simp_all [sgn, Complex.norm_real, mul_pow, abs_of_nonneg, Real.sqrt_nonneg] <;>
    field_simp <;> norm_num [h6]

/-- The measurement outcomes are exhaustive: the final state is a unit vector, so the two
probabilities sum to one. -/
