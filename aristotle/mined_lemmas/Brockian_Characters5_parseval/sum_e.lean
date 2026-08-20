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

lemma sum_e : ∑ a : ZMod 5, e a = 0 := by
  rw [sum_univ_zmod_five]
  show ω ^ (0 : ZMod 5).val + ω ^ (1 : ZMod 5).val + ω ^ (2 : ZMod 5).val + ω ^ (3 : ZMod 5).val
      + ω ^ (4 : ZMod 5).val = 0
  rw [show (0 : ZMod 5).val = 0 from rfl, show (1 : ZMod 5).val = 1 from rfl,
    show (2 : ZMod 5).val = 2 from rfl, show (3 : ZMod 5).val = 3 from rfl,
    show (4 : ZMod 5).val = 4 from rfl]
  linear_combination geom_sum_omega

/-- Orthogonality of the characters of `ZMod 5`. -/
