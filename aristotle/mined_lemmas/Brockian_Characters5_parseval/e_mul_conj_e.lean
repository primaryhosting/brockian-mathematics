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

open Complex

/-- The primitive fifth root of unity `exp (2πi/5)`. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e k = ω ^ k` on `ZMod 5`. -/

lemma e_mul_conj_e (a x y : ZMod 5) :
    e (a * x) * (starRingEnd ℂ) (e (a * y)) = e (a * (x - y)) := by
  rw [conj_e, ← e_add, mul_sub, sub_eq_add_neg]

