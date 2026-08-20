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

/-- A state of a two–qubit register: a complex amplitude for each computational
basis state `|x y⟩`, `x y : Bool`. -/
abbrev State := Bool × Bool → ℂ

/-- The sign `(-1)^b`. -/

theorem probZero_add_probOne (f : Bool → Bool) : probZero f + probOne f = 1 := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [probZero, probOne, deutschState_false, deutschState_true]
  cases hf0 : f false <;> cases hf1 : f true <;>
    simp [div_pow, abs_of_pos hs, mul_pow, hs2] <;> norm_num

end QC

