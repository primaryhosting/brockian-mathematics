import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

lemma e_eq_stdAddChar (a : ZMod 5) : e a = ZMod.stdAddChar a := by
  have h : ((a.val : ℤ) : ZMod 5) = a := by
    simp [ZMod.natCast_val, ZMod.intCast_cast]
  have h2 := ZMod.stdAddChar_coe (N := 5) (a.val : ℤ)
  rw [h] at h2
  rw [e, h2, omega, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Orthogonality of the additive characters of `ZMod 5`. -/
