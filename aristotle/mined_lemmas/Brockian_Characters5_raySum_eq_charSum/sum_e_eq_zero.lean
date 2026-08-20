/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e` of `ZMod 5` with values in `ℂ`, `e x = ω ^ x.val`. -/

lemma sum_e_eq_zero : ∑ b : ZMod 5, e b = 0 := by
  rw [sum_zmod_five]
  simp only [e, show (0 : ZMod 5).val = 0 from rfl, show (1 : ZMod 5).val = 1 from rfl,
    show (2 : ZMod 5).val = 2 from rfl, show (3 : ZMod 5).val = 3 from rfl,
    show (4 : ZMod 5).val = 4 from rfl]
  simpa using geom_omega

/-- Orthogonality: the character sum `∑_a e (a * x)` is `5` when `x = 0` and `0` otherwise. -/
