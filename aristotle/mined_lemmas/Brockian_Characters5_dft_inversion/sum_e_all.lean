import Mathlib

/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

/-- A primitive fifth root of unity. -/

lemma sum_e_all : ∑ a : ZMod 5, e a = 0 := by
  rw [sum_zmod5]
  simp only [e, show ZMod.val (0 : ZMod 5) = 0 from rfl, show ZMod.val (1 : ZMod 5) = 1 from rfl,
    show ZMod.val (2 : ZMod 5) = 2 from rfl, show ZMod.val (3 : ZMod 5) = 3 from rfl,
    show ZMod.val (4 : ZMod 5) = 4 from rfl, pow_zero, pow_one]
  linear_combination sum_omega

/-- Orthogonality of the characters on `ZMod 5`. -/
