import Mathlib

/-!
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
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

namespace Brockian.Characters5

/-- The primitive fifth root of unity `exp (2πi/5)`. -/

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : e k * e (-k) = 1 := by rw [← e_add]; simp [e_zero]
  have h2 : (e k)⁻¹ = (starRingEnd ℂ) (e k) := Complex.inv_eq_conj (norm_e k)
  rw [← h2]
  exact inv_eq_of_mul_eq_one_right h1

/-- Orthogonality of characters on `ZMod 5`. -/
